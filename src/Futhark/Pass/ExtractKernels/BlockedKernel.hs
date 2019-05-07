{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Futhark.Pass.ExtractKernels.BlockedKernel
       ( segRed
       , nonSegRed
       , segScan
       , segGenRed

       , streamRed
       , streamMap

       , mapKernel
       , KernelInput(..)
       , readKernelInput

       , injectSOACS

       , getSize
       , segThread
       , mkSegSpace
       )
       where

import Control.Monad
import Data.Maybe
import Data.List

import Prelude hiding (quot)

import Futhark.Analysis.PrimExp
import Futhark.Analysis.Rephrase
import Futhark.Representation.AST
import qualified Futhark.Representation.SOACS.SOAC as SOAC
import Futhark.Representation.Kernels
       hiding (Prog, Body, Stm, Pattern, PatElem,
               BasicOp, Exp, Lambda, FunDef, FParam, LParam, RetType)
import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Transform.Rename

getSize :: (MonadBinder m, Op (Lore m) ~ HostOp (Lore m) (SOAC.SOAC (Lore m))) =>
           String -> SizeClass -> m SubExp
getSize desc size_class = do
  size_key <- nameFromString . pretty <$> newVName desc
  letSubExp desc $ Op $ GetSize size_key size_class

segThread :: (MonadBinder m, Op (Lore m) ~ HostOp (Lore m) (SOAC.SOAC (Lore m))) =>
             String -> m SegLevel
segThread desc =
  SegThread
    <$> (Count <$> getSize (desc ++ "_num_groups") SizeNumGroups)
    <*> (Count <$> getSize (desc ++ "_group_size") SizeGroup)

mkSegSpace :: MonadFreshNames m => [(VName, SubExp)] -> m SegSpace
mkSegSpace dims = SegSpace <$> newVName "phys_tid" <*> pure dims

-- | Given a chunked fold lambda that takes its initial accumulator
-- value as parameters, bind those parameters to the neutral element
-- instead.
kerneliseLambda :: MonadFreshNames m =>
                   [SubExp] -> Lambda Kernels -> m (Lambda Kernels)
kerneliseLambda nes lam = do
  thread_index <- newVName "thread_index"
  let thread_index_param = Param thread_index $ Prim int32
      (fold_chunk_param, fold_acc_params, fold_inp_params) =
        partitionChunkedFoldParameters (length nes) $ lambdaParams lam

      mkAccInit p (Var v)
        | not $ primType $ paramType p =
            mkLet [] [paramIdent p] $ BasicOp $ Copy v
      mkAccInit p x = mkLet [] [paramIdent p] $ BasicOp $ SubExp x
      acc_init_bnds = stmsFromList $ zipWith mkAccInit fold_acc_params nes
  return lam { lambdaBody = insertStms acc_init_bnds $
                            lambdaBody lam
             , lambdaParams = thread_index_param :
                              fold_chunk_param :
                              fold_inp_params
             }

prepareRedOrScan :: (MonadBinder m, Lore m ~ Kernels) =>
                    SubExp
                 -> Lambda Kernels
                 -> [VName] -> [(VName, SubExp)] -> [KernelInput]
                 -> m (SegSpace, KernelBody Kernels)
prepareRedOrScan w map_lam arrs ispace inps = do
  gtid <- newVName "gtid"
  space <- mkSegSpace $ ispace ++ [(gtid, w)]
  kbody <- fmap (uncurry (flip (KernelBody ()))) $ runBinder $
          localScope (scopeOfSegSpace space) $ do
    mapM_ (addStm <=< readKernelInput) inps
    forM_ (zip (lambdaParams map_lam) arrs) $ \(p, arr) -> do
      arr_t <- lookupType arr
      letBindNames_ [paramName p] $
        BasicOp $ Index arr $ fullSlice arr_t [DimFix $ Var gtid]
    map ThreadsReturn <$> bodyBind (lambdaBody map_lam)

  return (space, kbody)

segRed :: (MonadFreshNames m, HasScope Kernels m) =>
          Pattern Kernels
       -> SubExp -- segment size
       -> Commutativity
       -> Lambda Kernels -> Lambda Kernels
       -> [SubExp] -> [VName]
       -> [(VName, SubExp)] -- ispace = pair of (gtid, size) for the maps on "top" of this reduction
       -> [KernelInput]     -- inps = inputs that can be looked up by using the gtids from ispace
       -> m (Stms Kernels)
segRed pat w comm reduce_lam map_lam nes arrs ispace inps = runBinder_ $ do
  (kspace, kbody) <- prepareRedOrScan w map_lam arrs ispace inps
  lvl <- segThread "segred"
  letBind_ pat $ Op $ SegOp $
    SegRed lvl kspace comm reduce_lam nes (lambdaReturnType map_lam) kbody

segScan :: (MonadFreshNames m, HasScope Kernels m) =>
           Pattern Kernels
        -> SubExp -- segment size
        -> Lambda Kernels -> Lambda Kernels
        -> [SubExp] -> [VName]
        -> [(VName, SubExp)] -- ispace = pair of (gtid, size) for the maps on "top" of this scan
        -> [KernelInput]     -- inps = inputs that can be looked up by using the gtids from ispace
        -> m (Stms Kernels)
segScan pat w scan_lam map_lam nes arrs ispace inps = runBinder_ $ do
  (kspace, kbody) <- prepareRedOrScan w map_lam arrs ispace inps
  lvl <- segThread "segscan"
  letBind_ pat $ Op $ SegOp $
    SegScan lvl kspace scan_lam nes (lambdaReturnType map_lam) kbody

dummyDim :: (MonadFreshNames m, MonadBinder m) =>
            Pattern Kernels
         -> m (Pattern Kernels, [(VName, SubExp)], m ())
dummyDim pat = do
  -- We add a unit-size segment on top to ensure that the result
  -- of the SegRed is an array, which we then immediately index.
  -- This is useful in the case that the value is used on the
  -- device afterwards, as this may save an expensive
  -- host-device copy (scalars are kept on the host, but arrays
  -- may be on the device).
  let addDummyDim t = t `arrayOfRow` intConst Int32 1
  pat' <- fmap addDummyDim <$> renamePattern pat
  dummy <- newVName "dummy"
  let ispace = [(dummy, intConst Int32 1)]

  return (pat', ispace,
          forM_ (zip (patternNames pat') (patternNames pat)) $ \(from, to) -> do
             from_t <- lookupType from
             letBindNames_ [to] $ BasicOp $ Index from $
               fullSlice from_t [DimFix $ intConst Int32 0])

nonSegRed :: (MonadFreshNames m, HasScope Kernels m) =>
             Pattern Kernels
          -> SubExp
          -> Commutativity
          -> Lambda Kernels
          -> Lambda Kernels
          -> [SubExp]
          -> [VName]
          -> m (Stms Kernels)
nonSegRed pat w comm red_lam map_lam nes arrs = runBinder_ $ do
  (pat', ispace, read_dummy) <- dummyDim pat
  addStms =<< segRed pat' w comm red_lam map_lam nes arrs ispace []
  read_dummy

prepareStream :: (MonadBinder m, Lore m ~ Kernels) =>
                 KernelSize
              -> [(VName, SubExp)]
              -> SubExp
              -> Commutativity
              -> Lambda Kernels
              -> [SubExp]
              -> [VName]
              -> m (SubExp, SegSpace, [Type], KernelBody Kernels)
prepareStream size ispace w comm fold_lam nes arrs = do
  let (KernelSize _ _ elems_per_thread _ num_threads) = size
  let (ordering, split_ordering) =
        case comm of Commutative -> (Disorder, SplitStrided num_threads)
                     Noncommutative -> (InOrder, SplitContiguous)

  fold_lam' <- kerneliseLambda nes fold_lam

  elems_per_thread_32 <- asIntS Int32 elems_per_thread

  gtid <- newVName "gtid"
  space <- mkSegSpace $ ispace ++ [(gtid, num_threads)]
  kbody <- fmap (uncurry (flip (KernelBody ()))) $ runBinder $
           localScope (scopeOfSegSpace space) $ do
    (chunk_red_pes, chunk_map_pes) <-
      blockedPerThread gtid w size ordering fold_lam' (length nes) arrs
    let concatReturns pe =
          ConcatReturns split_ordering w elems_per_thread_32 Nothing $ patElemName pe
    return (map (ThreadsReturn . Var . patElemName) chunk_red_pes ++
            map concatReturns chunk_map_pes)

  let (redout_ts, mapout_ts) = splitAt (length nes) $ lambdaReturnType fold_lam
      ts = redout_ts ++ map rowType mapout_ts

  return (num_threads, space, ts, kbody)

streamRed :: (MonadFreshNames m, HasScope Kernels m) =>
             Pattern Kernels
          -> SubExp
          -> Commutativity
          -> Lambda Kernels -> Lambda Kernels
          -> [SubExp] -> [VName]
          -> m (Stms Kernels)
streamRed pat w comm red_lam fold_lam nes arrs = runBinder_ $ do
  -- The strategy here is to rephrase the stream reduction as a
  -- non-segmented SegRed that does explicit chunking within its body.
  -- First, figure out how many threads to use for this.
  (_, size) <- blockedKernelSize =<< asIntS Int64 w

  let (redout_pes, mapout_pes) = splitAt (length nes) $ patternElements pat
  (redout_pat, ispace, read_dummy) <- dummyDim $ Pattern [] redout_pes
  let pat' = Pattern [] $ patternElements redout_pat ++ mapout_pes

  (_, kspace, ts, kbody) <- prepareStream size ispace w comm fold_lam nes arrs

  lvl <- segThread "stream_red"
  letBind_ pat' $ Op $ SegOp $ SegRed lvl kspace comm red_lam nes ts kbody

  read_dummy

-- Similar to streamRed, but without the last reduction.
streamMap :: (MonadFreshNames m, HasScope Kernels m) =>
              [String] -> [PatElem Kernels] -> SubExp
           -> Commutativity -> Lambda Kernels -> [SubExp] -> [VName]
           -> m ((SubExp, [VName]), Stms Kernels)
streamMap out_desc mapout_pes w comm fold_lam nes arrs = runBinder $ do
  (_, size) <- blockedKernelSize =<< asIntS Int64 w

  (threads, kspace, ts, kbody) <- prepareStream size [] w comm fold_lam nes arrs

  let redout_ts = take (length nes) ts

  redout_pes <- forM (zip out_desc redout_ts) $ \(desc, t) ->
    PatElem <$> newVName desc <*> pure (t `arrayOfRow` threads)

  let pat = Pattern [] $ redout_pes ++ mapout_pes
  lvl <- segThread "stream_map"
  letBind_ pat $ Op $ SegOp $ SegMap lvl kspace ts kbody

  return (threads, map patElemName redout_pes)

segGenRed :: (MonadFreshNames m, HasScope Kernels m) =>
             Pattern Kernels
          -> SubExp
          -> [(VName,SubExp)] -- ^ Segment indexes and sizes.
          -> [KernelInput]
          -> [GenReduceOp Kernels]
          -> Lambda Kernels -> [VName]
          -> m (Stms Kernels)
segGenRed pat arr_w ispace inps ops lam arrs = runBinder_ $ do
  gtid <- newVName "gtid"
  space <- mkSegSpace $ ispace ++ [(gtid, arr_w)]

  kbody <- fmap (uncurry (flip $ KernelBody ())) $ runBinder $
          localScope (scopeOfSegSpace space) $ do
    mapM_ (addStm <=< readKernelInput) inps
    forM_ (zip (lambdaParams lam) arrs) $ \(p, arr) -> do
      arr_t <- lookupType arr
      letBindNames_ [paramName p] $
        BasicOp $ Index arr $ fullSlice arr_t [DimFix $ Var gtid]
    map ThreadsReturn <$> bodyBind (lambdaBody lam)

  lvl <- segThread "seggenred"
  letBind_ pat $ Op $ SegOp $ SegGenRed lvl space ops (lambdaReturnType lam) kbody

blockedPerThread :: (MonadBinder m, Lore m ~ Kernels) =>
                    VName -> SubExp -> KernelSize -> StreamOrd -> Lambda Kernels
                 -> Int -> [VName]
                 -> m ([PatElem Kernels], [PatElem Kernels])
blockedPerThread thread_gtid w kernel_size ordering lam num_nonconcat arrs = do
  let (_, chunk_size, [], arr_params) =
        partitionChunkedKernelFoldParameters 0 $ lambdaParams lam

      ordering' =
        case ordering of InOrder -> SplitContiguous
                         Disorder -> SplitStrided $ kernelNumThreads kernel_size
      red_ts = take num_nonconcat $ lambdaReturnType lam
      map_ts = map rowType $ drop num_nonconcat $ lambdaReturnType lam

  per_thread <- asIntS Int32 $ kernelElementsPerThread kernel_size
  splitArrays (paramName chunk_size) (map paramName arr_params) ordering' w
    (Var thread_gtid) per_thread arrs

  chunk_red_pes <- forM red_ts $ \red_t -> do
    pe_name <- newVName "chunk_fold_red"
    return $ PatElem pe_name red_t
  chunk_map_pes <- forM map_ts $ \map_t -> do
    pe_name <- newVName "chunk_fold_map"
    return $ PatElem pe_name $ map_t `arrayOfRow` Var (paramName chunk_size)

  let (chunk_red_ses, chunk_map_ses) =
        splitAt num_nonconcat $ bodyResult $ lambdaBody lam

  addStms $
    bodyStms (lambdaBody lam) <>
    stmsFromList
    [ Let (Pattern [] [pe]) (defAux ()) $ BasicOp $ SubExp se
    | (pe,se) <- zip chunk_red_pes chunk_red_ses ] <>
    stmsFromList
    [ Let (Pattern [] [pe]) (defAux ()) $ BasicOp $ SubExp se
    | (pe,se) <- zip chunk_map_pes chunk_map_ses ]

  return (chunk_red_pes, chunk_map_pes)

splitArrays :: (MonadBinder m, Lore m ~ Kernels) =>
               VName -> [VName]
            -> SplitOrdering -> SubExp -> SubExp -> SubExp -> [VName]
            -> m ()
splitArrays chunk_size split_bound ordering w i elems_per_i arrs = do
  letBindNames_ [chunk_size] $ Op $ SplitSpace ordering w i elems_per_i
  case ordering of
    SplitContiguous     -> do
      offset <- letSubExp "slice_offset" $ BasicOp $ BinOp (Mul Int32) i elems_per_i
      zipWithM_ (contiguousSlice offset) split_bound arrs
    SplitStrided stride -> zipWithM_ (stridedSlice stride) split_bound arrs
  where contiguousSlice offset slice_name arr = do
          arr_t <- lookupType arr
          let slice = fullSlice arr_t [DimSlice offset (Var chunk_size) (constant (1::Int32))]
          letBindNames_ [slice_name] $ BasicOp $ Index arr slice

        stridedSlice stride slice_name arr = do
          arr_t <- lookupType arr
          let slice = fullSlice arr_t [DimSlice i (Var chunk_size) stride]
          letBindNames_ [slice_name] $ BasicOp $ Index arr slice

data KernelSize = KernelSize { kernelWorkgroups :: SubExp
                               -- ^ Int32
                             , kernelWorkgroupSize :: SubExp
                               -- ^ Int32
                             , kernelElementsPerThread :: SubExp
                               -- ^ Int64
                             , kernelTotalElements :: SubExp
                               -- ^ Int64
                             , kernelNumThreads :: SubExp
                               -- ^ Int32
                             }
                deriving (Eq, Ord, Show)

numberOfGroups :: MonadBinder m => SubExp -> SubExp -> SubExp -> m (SubExp, SubExp)
numberOfGroups w group_size max_num_groups = do
  -- If 'w' is small, we launch fewer groups than we normally would.
  -- We don't want any idle groups.
  w_div_group_size <- letSubExp "w_div_group_size" =<<
    eDivRoundingUp Int64 (eSubExp w) (eSubExp group_size)
  -- We also don't want zero groups.
  num_groups_maybe_zero <- letSubExp "num_groups_maybe_zero" $ BasicOp $ BinOp (SMin Int64)
                           w_div_group_size max_num_groups
  num_groups <- letSubExp "num_groups" $
                BasicOp $ BinOp (SMax Int64) (intConst Int64 1)
                num_groups_maybe_zero
  num_threads <-
    letSubExp "num_threads" $ BasicOp $ BinOp (Mul Int64) num_groups group_size
  return (num_groups, num_threads)

blockedKernelSize :: (MonadBinder m, Lore m ~ Kernels) =>
                     SubExp -> m (SubExp, KernelSize)
blockedKernelSize w = do
  group_size <- getSize "group_size" SizeGroup
  max_num_groups <- getSize "max_num_groups" SizeNumGroups

  group_size' <- asIntS Int64 group_size
  max_num_groups' <- asIntS Int64 max_num_groups
  (num_groups, num_threads) <- numberOfGroups w group_size' max_num_groups'
  num_groups' <- asIntS Int32 num_groups
  num_threads' <- asIntS Int32 num_threads

  per_thread_elements <-
    letSubExp "per_thread_elements" =<<
    eDivRoundingUp Int64 (toExp =<< asIntS Int64 w) (toExp =<< asIntS Int64 num_threads)

  return (max_num_groups,
          KernelSize num_groups' group_size per_thread_elements w num_threads')

mapKernelSkeleton :: (HasScope Kernels m, MonadFreshNames m) =>
                     [(VName, SubExp)] -> [KernelInput]
                  -> m (SegSpace, Stms Kernels)
mapKernelSkeleton ispace inputs = do
  read_input_bnds <- stmsFromList <$> mapM readKernelInput inputs

  space <- mkSegSpace ispace
  return (space, read_input_bnds)

mapKernel :: (HasScope Kernels m, MonadFreshNames m) =>
             SubExp -> [(VName, SubExp)] -> [KernelInput]
          -> [Type] -> KernelBody Kernels
          -> m (SegOp Kernels, Stms Kernels)
mapKernel w ispace inputs rts (KernelBody () kstms krets) = runBinder $ do
  (space, read_input_stms) <- mapKernelSkeleton ispace inputs

  let kbody' = KernelBody () (read_input_stms <> kstms) krets

  group_size <- getSize "segmap_group_size" SizeGroup
  num_groups <- letSubExp "segmap_num_groups" =<<
                eDivRoundingUp Int32 (eSubExp w) (eSubExp group_size)

  let lvl = SegThread (Count num_groups) (Count group_size)
  return $ SegMap lvl space rts kbody'

data KernelInput = KernelInput { kernelInputName :: VName
                               , kernelInputType :: Type
                               , kernelInputArray :: VName
                               , kernelInputIndices :: [SubExp]
                               }
                 deriving (Show)

readKernelInput :: (ExpAttr lore ~ (), LetAttr lore ~ Type,
                    HasScope anylore m, Monad m) =>
                   KernelInput -> m (Stm lore)
readKernelInput inp = do
  let pe = PatElem (kernelInputName inp) $ kernelInputType inp
  arr_t <- lookupType $ kernelInputArray inp
  return $ Let (Pattern [] [pe]) (defAux ()) $
    BasicOp $ Index (kernelInputArray inp) $
    fullSlice arr_t $ map DimFix $ kernelInputIndices inp

injectSOACS :: (Monad m,
                SameScope from to,
                ExpAttr from ~ ExpAttr to,
                BodyAttr from ~ BodyAttr to,
                RetType from ~ RetType to,
                BranchType from ~ BranchType to,
                Op from ~ SOAC from) =>
               (SOAC to -> Op to) -> Rephraser m from to
injectSOACS f = Rephraser { rephraseExpLore = return
                          , rephraseBodyLore = return
                          , rephraseLetBoundLore = return
                          , rephraseFParamLore = return
                          , rephraseLParamLore = return
                          , rephraseOp = fmap f . onSOAC
                          , rephraseRetType = return
                          , rephraseBranchType = return
                          }
  where onSOAC = SOAC.mapSOACM mapper
        mapper = SOAC.SOACMapper { SOAC.mapOnSOACSubExp = return
                                 , SOAC.mapOnSOACVName = return
                                 , SOAC.mapOnSOACLambda = rephraseLambda $ injectSOACS f
                                 }
