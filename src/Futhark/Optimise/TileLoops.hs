{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-- | Perform a restricted form of loop tiling within kernel streams.
-- We only tile primitive types, to avoid excessive local memory use.
module Futhark.Optimise.TileLoops
       ( tileLoops )
       where

import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.List

import Prelude hiding (quot)

import Futhark.MonadFreshNames
import Futhark.Representation.Kernels
import Futhark.Transform.Rename
import Futhark.Transform.Substitute
import Futhark.Pass
import Futhark.Tools
import Futhark.Optimise.TileLoops.RegTiling3D
import Futhark.Util.IntegralExp

tileLoops :: Pass Kernels Kernels
tileLoops = Pass "tile loops" "Tile stream loops inside kernels" $
            fmap Prog . mapM optimiseFunDef . progFunctions

optimiseFunDef :: MonadFreshNames m => FunDef Kernels -> m (FunDef Kernels)
optimiseFunDef fundec = do
  body' <- modifyNameSource $ runState $
           runReaderT m (scopeOfFParams (funDefParams fundec))
  return fundec { funDefBody = body' }
  where m = optimiseBody $ funDefBody fundec

type TileM = ReaderT (Scope Kernels) (State VNameSource)

optimiseBody :: Body Kernels -> TileM (Body Kernels)
optimiseBody (Body () bnds res) = localScope (scopeOf bnds) $
  Body () <$> (mconcat <$> mapM optimiseStm (stmsToList bnds)) <*> pure res

optimiseStm :: Stm Kernels -> TileM (Stms Kernels)
optimiseStm stm@(Let pat aux (Op (SegOp (SegMap lvl@SegThread{} space ts kbody)))) = do
  res3dtiling <- doRegTiling3D stm
  case res3dtiling of
    Just (extra_bnds, stmt') -> return $ extra_bnds <> oneStm stmt'
    Nothing -> do
      (extra_stms, lvl', space', kbody') <- tileInKernelBody mempty initial_variance lvl space ts kbody
      return $ extra_stms <>
        oneStm (Let pat aux $ Op $ SegOp $ SegMap lvl' space' ts kbody')
  where initial_variance = M.map mempty $ scopeOfSegSpace space

optimiseStm (Let pat aux e) =
  pure <$> (Let pat aux <$> mapExpM optimise e)
  where optimise = identityMapper { mapOnBody = const optimiseBody }

tileInKernelBody :: Names -> VarianceTable
                 -> SegLevel -> SegSpace -> [Type] -> KernelBody Kernels
                 -> TileM (Stms Kernels, SegLevel, SegSpace, KernelBody Kernels)
tileInKernelBody branch_variant initial_variance lvl initial_kspace ts (KernelBody () kstms kres)
  | Just res <- mapM isSimpleResult kres = do
      (extra_stms, lvl', kspace', kbody) <-
        tileInBody branch_variant initial_variance lvl initial_kspace ts $
        Body () kstms res
      return (extra_stms, lvl', kspace', kbody)
  | otherwise =
      return (mempty, lvl, initial_kspace, KernelBody () kstms kres)
  where isSimpleResult (ThreadsReturn se) = Just se
        isSimpleResult _ = Nothing

tileInBody :: Names -> VarianceTable
           -> SegLevel -> SegSpace -> [Type] -> Body Kernels
           -> TileM (Stms Kernels, SegLevel, SegSpace, KernelBody Kernels)
tileInBody branch_variant initial_variance lvl initial_kspace ts body = do
  (extra_stms, lvl', kspace', body') <-
    tileInStms branch_variant initial_variance lvl initial_kspace ts body
  return (extra_stms, lvl', kspace', body')

tileInStms :: Names -> VarianceTable
           -> SegLevel -> SegSpace -> [Type] -> Body Kernels
           -> TileM (Stms Kernels, SegLevel, SegSpace, KernelBody Kernels)
tileInStms branch_variant initial_variance initial_lvl initial_space res_ts (Body () initial_kstms stms_res) =
  descend mempty $ stmsToList initial_kstms
  where
    variance = varianceInStms initial_variance initial_kstms

    descend prestms [] =
      return (mempty, initial_lvl, initial_space, KernelBody () prestms $ map ThreadsReturn stms_res)
    descend prestms (stm:poststms)
      -- 1D tiling of redomap.
      | [dim] <- unSegSpace initial_space,
        Just (w, arrs, form) <- tileable variance stm =
          tile1D initial_lvl prestms res_ts (stmPattern stm)
          dim w form arrs poststms stms_res

      -- 1D tiling of redomap.
      | [dim_x, dim_y] <- unSegSpace initial_space,
        Just (w, arrs, form) <- tileable variance stm =
          tile2D initial_lvl prestms res_ts (stmPattern stm)
          dim_x dim_y  w form arrs poststms stms_res

      | otherwise =
          localScope (scopeOf stm) $
          descend (prestms <> oneStm stm) poststms

tileable :: VarianceTable -> Stm Kernels
         -> Maybe (SubExp, [VName],
                   (Commutativity, Lambda Kernels, [SubExp], Lambda Kernels))
tileable variance stm
  | Op (OtherOp (Screma w form arrs)) <- stmExp stm,
    Just (red_comm, red_lam, red_nes, map_lam) <- isRedomapSOAC form,
    not $ null arrs,
    all (S.null . flip (M.findWithDefault mempty) variance) arrs,
    all primType $ lambdaReturnType map_lam,
    all (primType . paramType) $ lambdaParams map_lam =
      Just (w, arrs, (red_comm, red_lam, red_nes, map_lam))
  | otherwise =
      Nothing

liveSet :: FreeIn a => Stms Kernels -> a -> Names
liveSet stms after =
  S.fromList (concatMap (patternNames . stmPattern) stms) `S.intersection`
  freeIn after

data TileKind = TilePartial | TileFull

segMap1D :: String
         -> SegLevel
         -> (VName -> Binder Kernels [SubExp])
         -> Binder Kernels [VName]
segMap1D desc lvl f = do
  ltid <- newVName "ltid"
  ltid_flat <- newVName "ltid_flat"
  let space = SegSpace ltid_flat [(ltid, unCount $ segGroupSize lvl)]

  ((ts, res), stms) <- runBinder $ do
    res <- f ltid
    ts <- mapM subExpType res
    return (ts, res)

  letTupExp desc $ Op $ SegOp $
    SegMap lvl space ts $ KernelBody () stms $ map ThreadsReturn res

readTile1D :: TileKind
           -> SubExp -> SubExp
           -> Count NumGroups SubExp -> Count GroupSize SubExp
           -> [VName]
           -> Binder Kernels [VName]
readTile1D kind tile_id tile_size num_groups group_size arrs = do
  arr_ts <- mapM lookupType arrs
  let tile_ts = map rowType arr_ts
      w = arraysSize 0 arr_ts

  segMap1D "full_tile" (SegThread num_groups group_size) $ \ltid -> do
    j <- letSubExp "j" =<<
         toExp (primExpFromSubExp int32 tile_id *
                primExpFromSubExp int32 tile_size +
                LeafExp ltid int32)
    let readTileElem arr =
          -- No need for fullSlice because we are tiling only prims.
          letExp "tile_elem" $ BasicOp $ Index arr [DimFix j]
    fmap (map Var) $
      case kind of
        TilePartial ->
          letTupExp "pre" =<< eIf (toExp $ primExpFromSubExp int32 j .<.
                                   primExpFromSubExp int32 w)
          (resultBody <$> mapM (fmap Var . readTileElem) arrs)
          (eBody $ map eBlank tile_ts)
        TileFull ->
          mapM readTileElem arrs

processTile1D :: (VName -> Binder Kernels Substitutions)
              -> VName -> VName -> SubExp
              -> Commutativity -> Lambda Kernels -> Lambda Kernels
              -> Count NumGroups SubExp -> Count GroupSize SubExp
              -> [VName] -> [VName]
              -> Binder Kernels [VName]
processTile1D
  readPreludeValues gid gtid w
  red_comm red_lam map_lam num_groups group_size tile accs = do

  tile_size <- arraysSize 0 <$> mapM lookupType tile

  segMap1D "acc" (SegThreadScalar num_groups group_size) $ \ltid -> do
    -- Reconstruct the original gtid from gid and ltid.
    gtid' <- letExp "gtid" =<<
             toExp (LeafExp gid int32 *
                    primExpFromSubExp int32 (unCount group_size) +
                    LeafExp ltid int32)

    substs <- readPreludeValues ltid

    -- We replace the neutral elements with the
    -- accumulators (this is OK because the parallel
    -- semantics are not used after this point).
    thread_accs <- forM accs $ \acc ->
      letSubExp "acc" $ BasicOp $ Index acc [DimFix $ Var ltid]
    let form' = redomapSOAC red_comm red_lam thread_accs map_lam

    fmap (map Var) $
      letTupExp "acc" =<< eIf (toExp $ LeafExp gtid' int32 .<. primExpFromSubExp int32 w)
      (eBody [pure $ substituteNames (M.insert gtid gtid' substs) $
              Op $ OtherOp $ Screma tile_size form' tile])
      (resultBodyM thread_accs)

processResidualTile1D :: (MonadBinder m, Lore m ~ Kernels) =>
                         Count NumGroups SubExp -> Count GroupSize SubExp
                      -> VName -> VName
                      -> Commutativity -> Lambda Kernels -> Lambda Kernels
                      -> (VName -> Binder Kernels Substitutions)
                      -> SubExp -> SubExp -> [VName] -> SubExp -> [VName]
                      -> m [VName]
processResidualTile1D
  num_groups group_size gid gtid red_comm red_lam map_lam
  readPreludeValues num_whole_tiles tile_size accs w arrs = do
  -- The number of residual elements that are not covered by
  -- the whole tiles.
  residual_input <- letSubExp "residual_input" $
    BasicOp $ BinOp (SRem Int32) w tile_size

  letTupExp "acc_after_residual" =<<
    eIf (toExp $ primExpFromSubExp int32 residual_input .==. 0)
    (resultBodyM $ map Var accs)
    (nonemptyTile residual_input)

  where
    nonemptyTile residual_input = runBodyBinder $ do
      -- Collectively construct a tile.  Threads that are out-of-bounds
      -- provide a blank dummy value.
      full_tile <- readTile1D TilePartial
                   num_whole_tiles tile_size num_groups group_size arrs
      tile <- forM full_tile $ \tile ->
        letExp "partial_tile" $ BasicOp $ Index tile
        [DimSlice (intConst Int32 0) residual_input (intConst Int32 1)]

      -- Now each thread performs a traversal of the tile and
      -- updates its accumulator.
      resultBody . map Var <$> processTile1D
        readPreludeValues gid gtid w
        red_comm red_lam map_lam num_groups group_size tile accs

tile1D :: SegLevel -> Stms Kernels -> [Type] -> Pattern Kernels
       -> (VName, SubExp)
       -> SubExp -> (Commutativity, Lambda Kernels, [SubExp], Lambda Kernels) -> [VName]
       -> [Stm Kernels] -> [SubExp]
       -> TileM (Stms Kernels, SegLevel, SegSpace, KernelBody Kernels)
tile1D initial_lvl prestms res_ts pat (gtid, kdim) w form arrs poststms poststms_res = do
  -- Figure out which of values produced by the prelude
  -- statements are still alive.
  let prestms_live =
        S.toList $ liveSet prestms $
        freeIn poststms <> freeIn w <>
        freeIn red_lam <> freeIn red_nes <> freeIn map_lam
      group_size = unCount $ segGroupSize initial_lvl
      red_ts = lambdaReturnType red_lam
      (red_comm, red_lam, red_nes, map_lam) = form

  gid <- newVName "gid"

  (stms_res_arrs, kstms) <- runBinder $ do

    -- Create a SegMap that takes care of the prelude for every thread.
    let prelude_lvl = SegThreadScalar (segNumGroups initial_lvl) (segGroupSize initial_lvl)
    (prestms_live_arrs, mergeinits) <- fmap (splitAt (length prestms_live)) $
                                       segMap1D "prelude" prelude_lvl $ \ltid -> do
      -- Reconstruct the original gtid from gid and ltid.
      gtid' <- letExp "gtid" =<<
               toExp (LeafExp gid int32 * primExpFromSubExp int32 group_size +
                      LeafExp ltid int32)
      ts <- mapM lookupType prestms_live
      fmap (map Var) $ letTupExp "pre" =<<
        eIf (toExp $ LeafExp gtid' int32 .<. primExpFromSubExp int32 kdim)
        (do addStms $ substituteNames (M.singleton gtid gtid') prestms
            resultBodyM $ map Var prestms_live ++ red_nes)
        (eBody $ map eBlank $ ts ++ red_ts)

    -- Make the per-thread prelude results available.
    let readPreludeValues ltid =
          fmap mconcat $ forM (zip prestms_live_arrs prestms_live) $ \(arr, v) -> do
          arr_t <- lookupType arr
          M.singleton v <$> letExp (baseString v)
            (BasicOp $ Index arr $ fullSlice arr_t [DimFix $ Var ltid])

    merge <- forM (zip (lambdaParams red_lam) mergeinits) $ \(p, mergeinit) ->
      (,) <$>
      newParam (baseString (paramName p) ++ "_merge")
      (paramType p `arrayOfRow` group_size `toDecl` Unique) <*>
      pure (Var mergeinit)

    let tile_size = group_size

    -- Number of whole tiles that fit in the input.
    num_whole_tiles <- letSubExp "num_whole_tiles" $
      BasicOp $ BinOp (SQuot Int32) w tile_size

    i <- newVName "i"
    let loopform = ForLoop i Int32 num_whole_tiles []
    loopbody <- runBodyBinder $ inScopeOf loopform $
                localScope (scopeOfFParams $ map fst merge) $ do

      -- Collectively read a tile.
      tile <- readTile1D TileFull (Var i) tile_size
              (segNumGroups initial_lvl) (segGroupSize initial_lvl) arrs

      -- Now each thread performs a traversal of the tile and
      -- updates its accumulator.
      resultBody . map Var <$>
        processTile1D readPreludeValues gid gtid w
        red_comm red_lam map_lam
        (segNumGroups initial_lvl) (segGroupSize initial_lvl) tile
        (map (paramName . fst) merge)

    accs <- letTupExp "accs" $ DoLoop [] merge loopform loopbody

    -- We possibly have to traverse a residual tile.
    red_lam' <- renameLambda red_lam
    map_lam' <- renameLambda map_lam
    accs' <- processResidualTile1D (segNumGroups initial_lvl) (segGroupSize initial_lvl)
             gid gtid red_comm red_lam' map_lam' readPreludeValues
             num_whole_tiles tile_size accs w arrs

    -- Create a SegMap that takes care of the postlude for every thread.
    let postlude_lvl = SegThreadScalar (segNumGroups initial_lvl) (segGroupSize initial_lvl)
    segMap1D "thread_res" postlude_lvl $ \ltid -> do
      -- Read our per-thread result from the tiled loop.
      forM_ (zip (patternNames pat) accs') $ \(us, everyone) ->
        letBindNames_ [us] $ BasicOp $ Index everyone [DimFix $ Var ltid]

      -- Reconstruct the original gtid from gid and ltid.
      gtid' <- letExp "gtid" =<<
               toExp (LeafExp gid int32 * primExpFromSubExp int32 group_size +
                      LeafExp ltid int32)

      substs <- readPreludeValues ltid

      fmap (map Var) $ letTupExp "pre" =<<
        eIf (toExp $ LeafExp gtid' int32 .<. primExpFromSubExp int32 kdim)
        (do addStms $ stmsFromList $ substituteNames (M.insert gtid gtid' substs) poststms
            resultBodyM poststms_res)
        (eBody $ map eBlank res_ts)

  gid_flat <- newVName "gid_flat"
  let lvl = SegGroup (segNumGroups initial_lvl) (segGroupSize initial_lvl)
      space = SegSpace gid_flat [(gid, unCount $ segNumGroups lvl)]
      new_res = map (ConcatReturns SplitContiguous kdim group_size Nothing) stms_res_arrs
  return (mempty, lvl, space, KernelBody () kstms new_res)

tile2D :: SegLevel -> Stms Kernels -> [Type] -> Pattern Kernels
       -> (VName, SubExp) -> (VName, SubExp)
       -> SubExp -> (Commutativity, Lambda Kernels, [SubExp], Lambda Kernels) -> [VName]
       -> [Stm Kernels] -> [SubExp]
       -> TileM (Stms Kernels, SegLevel, SegSpace, KernelBody Kernels)
tile2D initial_lvl prestms res_ts pat (gtid_x, kdim_x) (gtid_y, kdim_y) w form arrs poststms poststms_res = do
  -- Figure out which of values produced by the prelude
  -- statements are still alive.
  let prestms_live =
        S.toList $
        S.fromList (concatMap (patternNames . stmPattern) $
                     stmsToList prestms) `S.intersection`
        (freeIn poststms <> freeIn w <>
         freeIn red_lam <> freeIn red_nes <> freeIn map_lam)
      (red_comm, red_lam, red_nes, map_lam) = form
      group_size = unCount $ segGroupSize initial_lvl
      red_ts = lambdaReturnType red_lam

  gid_x <- newVName "gid_x"
  gid_y <- newVName "gid_y"

  ((tile_size, num_threads, num_groups), prestms) <- runBinder $ do
    tile_size_key <-
      nameFromString . pretty <$> newVName "tile_size"
    tile_size <- letSubExp "tile_size" $ Op $ GetSize tile_size_key SizeTile

    (num_threads, num_groups) <-
      sufficientGroups [(kdim_x, tile_size), (kdim_y, tile_size)] group_size
    return (tile_size, num_threads, num_groups)

  let kstms = mempty
      stms_res_arrs = mempty

  gid_flat <- newVName "gid_flat"
  let lvl = SegGroup (segNumGroups initial_lvl) (segGroupSize initial_lvl)
      space = SegSpace gid_flat [(gid_x, unCount $ segNumGroups lvl)]
      new_res = map (ConcatReturns SplitContiguous undefined group_size Nothing) stms_res_arrs
  return (prestms, lvl, space, KernelBody () kstms new_res)

{-
        tileInKernelStatement (kspace, extra_bnds)
          (Let pat attr (Op (GroupStream w max_chunk lam accs arrs)))
          | max_chunk == w,
            not $ null arrs,
            chunk_size <- Var $ groupStreamChunkSize lam,
            arr_chunk_params <- groupStreamArrParams lam,
            maybe_1d_tiles <-
              zipWith (is1dTileable branch_variant kspace variance chunk_size) arrs arr_chunk_params,
            maybe_1_5d_tiles <-
              zipWith (is1_5dTileable branch_variant kspace variance chunk_size) arrs arr_chunk_params,
            Just mk_tilings <-
              zipWithM (<|>) maybe_1d_tiles maybe_1_5d_tiles = do

          (kspaces, arr_chunk_params', tile_kstms) <- unzip3 <$> sequence mk_tilings

          let (kspace', kspace_bnds) =
                case kspaces of
                  [] -> (kspace, mempty)
                  new_kspace : _ -> new_kspace
          Body () lam_kstms lam_res <- syncAtEnd $ groupStreamLambdaBody lam
          let lam_kstms' = mconcat tile_kstms <> lam_kstms
              group_size = spaceGroupSize kspace
              lam' = lam { groupStreamLambdaBody = Body () lam_kstms' lam_res
                         , groupStreamArrParams = arr_chunk_params'
                         }

          return ((kspace', extra_bnds <> kspace_bnds),
                  Let pat attr $ Op $ GroupStream w group_size lam' accs arrs)

        tileInKernelStatement (kspace, extra_bnds)
          (Let pat attr (Op (GroupStream w max_chunk lam accs arrs)))
          | w == max_chunk,
            not $ null arrs,
            FlatThreadSpace gspace <- spaceStructure kspace,
            chunk_size <- Var $ groupStreamChunkSize lam,
            arr_chunk_params <- groupStreamArrParams lam,

            Just mk_tilings <-
              zipWithM (is2dTileable branch_variant kspace variance chunk_size)
              arrs arr_chunk_params = do

          ((tile_size, tiled_group_size), tile_size_bnds) <- runBinder $ do
            tile_size_key <- nameFromString . pretty <$> newVName "tile_size"
            tile_size <- letSubExp "tile_size" $ Op $ GetSize tile_size_key SizeTile
            tiled_group_size <- letSubExp "tiled_group_size" $
                                BasicOp $ BinOp (Mul Int32) tile_size tile_size
            return (tile_size, tiled_group_size)

          let (tiled_gspace,untiled_gspace) = splitAt 2 $ reverse gspace
          -- Play with reversion to ensure we get increasing IDs for
          -- ltids.  This affects readability of generated code.
          untiled_gspace' <- fmap reverse $ forM (reverse untiled_gspace) $ \(gtid,gdim) -> do
            ltid <- newVName "ltid"
            return (gtid,gdim,
                    ltid, constant (1::Int32))
          tiled_gspace' <- fmap reverse $ forM (reverse tiled_gspace) $ \(gtid,gdim) -> do
            ltid <- newVName "ltid"
            return (gtid,gdim,
                    ltid, tile_size)
          let gspace' = reverse $ tiled_gspace' ++ untiled_gspace'

          -- We have to recalculate number of workgroups and
          -- number of threads to fit the new workgroup size.
          ((num_threads, num_groups), num_bnds) <-
            runBinder $ sufficientGroups gspace' tiled_group_size

          let kspace' = kspace { spaceStructure = NestedThreadSpace gspace'
                               , spaceGroupSize = tiled_group_size
                               , spaceNumThreads = num_threads
                               , spaceNumGroups = num_groups
                               }
              local_ids = map (\(_, _, ltid, _) -> ltid) gspace'

          (arr_chunk_params', tile_kstms) <-
            fmap unzip $ forM mk_tilings $ \mk_tiling ->
              mk_tiling tile_size local_ids

          Body () lam_kstms lam_res <- syncAtEnd $ groupStreamLambdaBody lam
          let lam_kstms' = mconcat tile_kstms <> lam_kstms
              lam' = lam { groupStreamLambdaBody = Body () lam_kstms' lam_res
                         , groupStreamArrParams = arr_chunk_params'
                         }

          return ((kspace', extra_bnds <> tile_size_bnds <> num_bnds),
                  Let pat attr $ Op $ GroupStream w tile_size lam' accs arrs)

        tileInKernelStatement (kspace, extra_bnds)
          (Let pat attr (Op (GroupStream w maxchunk lam accs arrs))) = do
          let branch_variant' = branch_variant <>
                                fromMaybe mempty (flip M.lookup variance =<< subExpVar w)
          (bnds, kspace', lam') <- tileInStreamLambda branch_variant' variance kspace lam
          return ((kspace', extra_bnds <> bnds),
                  Let pat attr $ Op $ GroupStream w maxchunk lam' accs arrs)
-}
{-
is1dTileable :: MonadFreshNames m =>
                Names -> KernelSpace -> VarianceTable -> SubExp -> VName -> LParam InKernel
             -> Maybe (m ((KernelSpace, Stms Kernels),
                           LParam InKernel,
                           Stms InKernel))
is1dTileable branch_variant kspace variance block_size arr block_param = do
  guard $ S.null $ M.findWithDefault mempty arr variance
  guard $ S.null branch_variant
  guard $ primType $ rowType $ paramType block_param

  return $ do
    (outer_block_param, kstms) <- tile1d kspace block_size block_param
    return ((kspace, mempty), outer_block_param, kstms)

is1_5dTileable :: (MonadFreshNames m, HasScope Kernels m) =>
                  Names -> KernelSpace -> VarianceTable
               -> SubExp -> VName -> LParam InKernel
               -> Maybe (m ((KernelSpace, Stms Kernels),
                            LParam InKernel,
                            Stms InKernel))
is1_5dTileable branch_variant kspace variance block_size arr block_param = do
  guard $ primType $ rowType $ paramType block_param

  (inner_gtid, inner_gdim) <- invariantToInnermostDimension
  mk_structure <-
    case spaceStructure kspace of
      NestedThreadSpace{} -> Nothing
      FlatThreadSpace gtids_and_gdims ->
        return $ do
          -- Force a functioning group size. XXX: not pretty.
          let n_dims = length gtids_and_gdims
          outer <- forM (take (n_dims-1) gtids_and_gdims) $ \(gtid, gdim) -> do
            ltid <- newVName "ltid"
            return (gtid, gdim, ltid, gdim)

          inner_ltid <- newVName "inner_ltid"
          inner_ldim <- newVName "inner_ldim"
          let compute_tiled_group_size =
                mkLet [] [Ident inner_ldim $ Prim int32] $
                BasicOp $ BinOp (SMin Int32) (spaceGroupSize kspace) inner_gdim
              structure = NestedThreadSpace $ outer ++ [(inner_gtid, inner_gdim,
                                                         inner_ltid, Var inner_ldim)]
          ((num_threads, num_groups), num_bnds) <- runBinder $ do
            threads_necessary <-
              letSubExp "threads_necessary" =<<
              foldBinOp (Mul Int32)
              (constant (1::Int32)) (map snd gtids_and_gdims)
            groups_necessary <-
              letSubExp "groups_necessary" =<<
              eDivRoundingUp Int32 (eSubExp threads_necessary) (eSubExp $ Var inner_ldim)
            num_threads <-
              letSubExp "num_threads" $
              BasicOp $ BinOp (Mul Int32) groups_necessary (Var inner_ldim)
            return (num_threads, groups_necessary)

          let kspace' = kspace { spaceGroupSize = Var inner_ldim
                               , spaceNumGroups = num_groups
                               , spaceNumThreads = num_threads
                               , spaceStructure = structure
                               }
          return (oneStm compute_tiled_group_size <> num_bnds,
                  kspace')
  return $ do
    (outer_block_param, kstms) <- tile1d kspace block_size block_param
    (structure_bnds, kspace') <- mk_structure
    return ((kspace', structure_bnds), outer_block_param, kstms)
  where invariantToInnermostDimension :: Maybe (VName, SubExp)
        invariantToInnermostDimension =
          case reverse $ spaceDimensions kspace of
            (i,d) : _
              | not $ i `S.member` M.findWithDefault mempty arr variance,
                not $ i `S.member` branch_variant -> Just (i,d)
            _ -> Nothing

tile1d :: MonadFreshNames m =>
          KernelSpace
       -> SubExp
       -> LParam InKernel
       -> m (LParam InKernel, Stms InKernel)
tile1d kspace block_size block_param = do
  outer_block_param <- do
    name <- newVName $ baseString (paramName block_param) ++ "_outer"
    return block_param { paramName = name }

  let ltid = spaceLocalId kspace
  read_elem_bnd <- do
    name <- newVName $ baseString (paramName outer_block_param) ++ "_elem"
    return $
      mkLet [] [Ident name $ rowType $ paramType outer_block_param] $
      BasicOp $ Index (paramName outer_block_param) [DimFix $ Var ltid]

  cid <- newVName "cid"
  let block_cspace = combineSpace [(cid, block_size)]
      block_pe =
        PatElem (paramName block_param) $ paramType outer_block_param
      write_block_stms =
        [ Let (Pattern [] [block_pe]) (defAux ()) $ Op $
          Combine block_cspace [patElemType pe] [] $
          Body () (oneStm read_elem_bnd) [Var $ patElemName pe]
        | pe <- patternElements $ stmPattern read_elem_bnd ]

  return (outer_block_param, stmsFromList write_block_stms)

is2dTileable :: MonadFreshNames m =>
                Names -> KernelSpace -> VarianceTable -> SubExp -> VName -> LParam InKernel
             -> Maybe (SubExp -> [VName] -> m (LParam InKernel, Stms InKernel))
is2dTileable branch_variant kspace variance block_size arr block_param = do
  guard $ primType $ rowType $ paramType block_param

  pt <- case rowType $ paramType block_param of
          Prim pt -> return pt
          _       -> Nothing
  inner_perm <- invariantToOneOfTwoInnerDims
  Just $ \tile_size local_is -> do
    let num_outer = length local_is - 2
        perm = [0..num_outer-1] ++ map (+num_outer) inner_perm
        invariant_i : variant_i : _ = reverse $ rearrangeShape perm local_is
        (global_i,global_d):_ = rearrangeShape inner_perm $ drop num_outer $ spaceDimensions kspace
    outer_block_param <- do
      name <- newVName $ baseString (paramName block_param) ++ "_outer"
      return block_param { paramName = name }

    elem_name <- newVName $ baseString (paramName outer_block_param) ++ "_elem"
    let read_elem_bnd = mkLet [] [Ident elem_name $ Prim pt] $
                        BasicOp $ Index (paramName outer_block_param) $
                        fullSlice (paramType outer_block_param) [DimFix $ Var invariant_i]

    cids <- replicateM (length local_is - num_outer) $ newVName "cid"
    let block_size_2d = Shape $ rearrangeShape inner_perm [tile_size, block_size]
        block_cspace = combineSpace $ zip cids $
                       rearrangeShape inner_perm [tile_size,block_size]

    block_name_2d <- newVName $ baseString (paramName block_param) ++ "_2d"
    let block_pe =
          PatElem block_name_2d $
          rowType (paramType outer_block_param) `arrayOfShape` block_size_2d
        write_block_stm =
         Let (Pattern [] [block_pe]) (defAux ()) $
          Op $ Combine block_cspace [Prim pt] [(global_i, global_d)] $
          Body () (oneStm read_elem_bnd) [Var elem_name]

    let index_block_kstms =
          [mkLet [] [paramIdent block_param] $
            BasicOp $ Index block_name_2d $
            rearrangeShape inner_perm $
            fullSlice (rearrangeType inner_perm $ patElemType block_pe)
            [DimFix $ Var variant_i]]

    return (outer_block_param,
            oneStm write_block_stm <> stmsFromList index_block_kstms)

  where invariantToOneOfTwoInnerDims :: Maybe [Int]
        invariantToOneOfTwoInnerDims = do
          (j,_) : (i,_) : _ <- Just $ reverse $ spaceDimensions kspace
          let variant_to = M.findWithDefault mempty arr variance
              branch_invariant = not $ S.member j branch_variant || S.member i branch_variant
          if branch_invariant && i `S.member` variant_to && not (j `S.member` variant_to) then
            Just [0,1]
          else if branch_invariant && j `S.member` variant_to && not (i `S.member` variant_to) then
            Just [1,0]
          else
            Nothing

syncAtEnd :: MonadFreshNames m => Body InKernel -> m (Body InKernel)
syncAtEnd (Body () stms res) = do
  (res', stms') <- (`runBinderT` mempty) $ do
    mapM_ addStm stms
    map Var <$> letTupExp "sync" (Op $ Barrier res)
  return $ Body () stms' res'
-}
-- | The variance table keeps a mapping from a variable name
-- (something produced by a 'Stm') to the kernel thread indices
-- that name depends on.  If a variable is not present in this table,
-- that means it is bound outside the kernel (and so can be considered
-- invariant to all dimensions).
type VarianceTable = M.Map VName Names

varianceInStms :: VarianceTable -> Stms Kernels -> VarianceTable
varianceInStms = foldl varianceInStm

varianceInStm :: VarianceTable -> Stm Kernels -> VarianceTable
varianceInStm variance bnd =
  foldl' add variance $ patternNames $ stmPattern bnd
  where add variance' v = M.insert v binding_variance variance'
        look variance' v = S.insert v $ M.findWithDefault mempty v variance'
        binding_variance = mconcat $ map (look variance) $ S.toList (freeIn bnd)

sufficientGroups :: MonadBinder m =>
                    [(SubExp, SubExp)] -> SubExp
                 -> m (SubExp, SubExp)
sufficientGroups gspace group_size = do
  groups_in_dims <- forM gspace $ \(gd, ld) ->
    letSubExp "groups_in_dim" =<< eDivRoundingUp Int32 (eSubExp gd) (eSubExp ld)
  num_groups <- letSubExp "num_groups" =<<
                foldBinOp (Mul Int32) (constant (1::Int32)) groups_in_dims
  num_threads <- letSubExp "num_threads" $
                 BasicOp $ BinOp (Mul Int32) num_groups group_size
  return (num_threads, num_groups)
