{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-- | Extract limited nested parallelism for execution inside
-- individual kernel workgroups.
module Futhark.Pass.ExtractKernels.Intragroup
  (intraGroupParallelise)
where

import Control.Monad.Identity
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Futhark.Analysis.Rephrase
import Futhark.Analysis.PrimExp.Convert
import Futhark.Representation.SOACS
import qualified Futhark.Representation.Kernels as Out
import Futhark.Representation.Kernels.Kernel
import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Analysis.DataDependencies
import Futhark.Pass.ExtractKernels.Distribution
import Futhark.Pass.ExtractKernels.BlockedKernel

-- | Convert the statements inside a map nest to kernel statements,
-- attempting to parallelise any remaining (top-level) parallel
-- statements.  Anything that is not a map, scan or reduction will
-- simply be sequentialised.  This includes sequential loops that
-- contain maps, scans or reduction.  In the future, we could probably
-- do something more clever.  Make sure that the amount of parallelism
-- to be exploited does not exceed the group size.  Further, as a hack
-- we also consider the size of all intermediate arrays as
-- "parallelism to be exploited" to avoid exploding local memory.
--
-- We distinguish between "minimum group size" and "maximum
-- exploitable parallelism".
intraGroupParallelise :: (MonadFreshNames m, LocalScope Out.Kernels m) =>
                         KernelNest -> Lambda
                      -> m (Maybe ((SubExp, SubExp), SubExp,
                                   Out.Stms Out.Kernels, Out.Stms Out.Kernels))
intraGroupParallelise knest lam = runMaybeT $ do
  (w_stms, w, ispace, inps) <- lift $ flatKernel knest
  let num_groups = w
      body = lambdaBody lam

  group_size <- newVName "computed_group_size"
  let intra_lvl = SegThread (Count w) (Count $ Var group_size)

  ltid <- newVName "ltid"
  let group_variant = S.fromList [ltid]
  (wss_min, wss_avail, kbody) <-
    lift $ localScope (scopeOfLParams $ lambdaParams lam) $
    intraGroupParalleliseBody intra_lvl (dataDependencies body) group_variant ltid body

  known_outside <- lift $ M.keys <$> askScope
  unless (all (`elem` known_outside) $ freeIn $ wss_min ++ wss_avail) $
    fail "Irregular parallelism"

  ((intra_avail_par, kspace, read_input_stms), prelude_stms) <- lift $ runBinder $ do
    let foldBinOp' _    []    = eSubExp $ intConst Int32 0
        foldBinOp' bop (x:xs) = foldBinOp bop x xs
    ws_min <- mapM (letSubExp "one_intra_par_min" <=< foldBinOp' (Mul Int32)) $
              filter (not . null) wss_min
    ws_avail <- mapM (letSubExp "one_intra_par_avail" <=< foldBinOp' (Mul Int32)) $
                filter (not . null) wss_avail

    -- The amount of parallelism available *in the worst case* is
    -- equal to the smallest parallel loop.
    intra_avail_par <- letSubExp "intra_avail_par" =<< foldBinOp' (SMin Int32) ws_avail

    -- The group size is either the maximum of the minimum parallelism
    -- exploited, or the desired parallelism (bounded by the max group
    -- size) in case there is no minimum.
    letBindNames_ [group_size] =<<
      if null ws_min
      then eBinOp (SMin Int32)
           (eSubExp =<< letSubExp "max_group_size" (Op $ Out.GetSizeMax Out.SizeGroup))
           (eSubExp intra_avail_par)
      else foldBinOp' (SMax Int32) ws_min

    let inputIsUsed input = kernelInputName input `S.member` freeIn body
        used_inps = filter inputIsUsed inps

    addStms w_stms
    read_input_stms <- mapM readKernelInput used_inps
    space <- mkSegSpace ispace
    return (intra_avail_par, space, read_input_stms)

  let kbody' = kbody { kernelBodyStms = stmsFromList read_input_stms <> kernelBodyStms kbody }

  -- The kernel itself is producing a "flat" result of shape
  -- [num_groups].  We must explicitly reshape it to match the shapes
  -- of our enclosing map-nests.
  let nested_pat = loopNestingPattern first_nest
      flatPatElem pat_elem = do
        let t' = arrayOfRow (length ispace `stripArray` patElemType pat_elem) num_groups
        name <- newVName $ baseString (patElemName pat_elem) ++ "_flat"
        return $ PatElem name t'
  flat_pat <- lift $ Pattern [] <$> mapM flatPatElem (patternValueElements nested_pat)

  let rts = map rowType $ patternTypes flat_pat
      lvl = SegGroup (Count num_groups) (Count $ Var group_size)
      kstm = Let flat_pat (StmAux cs ()) $ Op $ SegOp $ SegMap lvl kspace rts kbody'
      reshapeStm nested_pe flat_pe =
        Let (Pattern [] [nested_pe]) (StmAux cs ()) $
        BasicOp $ Reshape (map DimNew $ arrayDims $ patElemType nested_pe) $
        patElemName flat_pe
      reshape_stms = zipWith reshapeStm (patternElements nested_pat)
                                        (patternElements flat_pat)

  let intra_min_par = intra_avail_par
  return ((intra_min_par, intra_avail_par), Var group_size,
           prelude_stms, oneStm kstm <> stmsFromList reshape_stms)
  where first_nest = fst knest
        cs = loopNestingCertificates first_nest

data Env = Env { _localTID :: VName
               , _dataDeps :: Dependencies
               , _groupVariant :: Names
               }

type IntraGroupM = BinderT Out.Kernels (RWS Env (S.Set [SubExp], S.Set [SubExp]) VNameSource)

runIntraGroupM :: (MonadFreshNames m, HasScope Out.Kernels m) =>
                  Env -> IntraGroupM () -> m ([[SubExp]], [[SubExp]], Out.Stms Out.Kernels)
runIntraGroupM env m = do
  scope <- castScope <$> askScope
  modifyNameSource $ \src ->
    let (((), kstms), src', (ws_min, ws_avail)) = runRWS (runBinderT m scope) env src
    in ((S.toList ws_min, S.toList ws_avail, kstms), src')

parallelMin :: [SubExp] -> IntraGroupM ()
parallelMin ws = tell (S.singleton ws, S.singleton ws)

intraGroupBody :: SegLevel -> Body -> IntraGroupM (Out.Body Out.Kernels)
intraGroupBody lvl body = do
  stms <- collectStms_ $ mapM_ (intraGroupStm lvl) $ bodyStms body
  return $ mkBody stms $ bodyResult body

intraGroupStm :: SegLevel -> Stm -> IntraGroupM ()
intraGroupStm lvl stm@(Let pat _ e) = do
  Env ltid deps group_variant <- ask
  let groupInvariant (Var v) =
        S.null . S.intersection group_variant .
        flip (M.findWithDefault mempty) deps $ v
      groupInvariant Constant{} = True

  case e of
    -- Cosmin hack: previously, only for loops were supported,
    --              and only if `groupInvariant bound` holds;
    --              Let's see what can possibly go wrong if we
    --              completely generalize this (?)
    DoLoop ctx val form loopbody ->
          localScope (scopeOf form') $
          localScope (scopeOfFParams $ map fst $ ctx ++ val) $ do
          loopbody' <- intraGroupBody lvl loopbody
          letBind_ pat $ DoLoop ctx val form' loopbody'
              where form' = case form of
                              ForLoop i it bound inps -> ForLoop i it bound inps
                              WhileLoop cond          -> WhileLoop cond

    If cond tbody fbody ifattr
      | groupInvariant cond -> do
          tbody' <- intraGroupBody lvl tbody
          fbody' <- intraGroupBody lvl fbody
          letBind_ pat $ If cond tbody' fbody' ifattr

    Op (Screma w form arrs) | Just fun <- isMapSOAC form -> do
      body_stms <- collectStms_ $ do
        forM_ (zip (lambdaParams fun) arrs) $ \(p, arr) -> do
          arr_t <- lookupType arr
          letBindNames [paramName p] $ BasicOp $ Index arr $
            fullSlice arr_t [DimFix $ Var ltid]
        addStms $ fmap soacsStmToKernels $ bodyStms $ lambdaBody fun
      let comb_body = mkBody body_stms $ bodyResult $ lambdaBody fun
      ctid <- newVName "ctid"
      space <- mkSegSpace [(ctid, w)]
      letBind_ pat $ Op $ SegOp $
        Out.SegMap lvl space (lambdaReturnType fun) $
        bodyToKernelBody comb_body
      mapM_ (parallelMin . arrayDims) $ patternTypes pat
      parallelMin [w]

    Op (Screma w form arrs)
      | Just (scanfun, nes, mapfun) <- isScanomapSOAC form -> do
      let scanfun' = soacsLambdaToKernels scanfun
          mapfun' = soacsLambdaToKernels mapfun
      addStms =<< segScan pat w scanfun' mapfun' nes arrs [] []
      parallelMin [w]

    Op (Screma w form arrs)
      | Just (comm, redfun, nes, mapfun) <- isRedomapSOAC form -> do
      let redfun' = soacsLambdaToKernels redfun
          mapfun' = soacsLambdaToKernels mapfun
      addStms =<< segRed pat w comm redfun' mapfun' nes arrs [] []
      parallelMin [w]

    Op (Stream w (Sequential accs) lam arrs)
      | chunk_size_param : _ <- lambdaParams lam -> do
      types <- asksScope castScope
      ((), stream_bnds) <-
        runBinderT (sequentialStreamWholeArray pat w accs lam arrs) types
      let replace (Var v) | v == paramName chunk_size_param = w
          replace se = se
          replaceSets (x, y) = (S.map (map replace) x, S.map (map replace) y)
      censor replaceSets $ mapM_ (intraGroupStm lvl) stream_bnds
{-
    Op (Scatter w lam ivs dests) -> do
      parallelMin [w]
      ctid <- newVName "ctid"
      let cspace = Out.CombineSpace dests [(ctid, w)]
      body_stms <- collectStms_ $ do
        forM_ (zip (lambdaParams lam) ivs) $ \(p, arr) -> do
          arr_t <- lookupType arr
          letBindNames [paramName p] $ BasicOp $ Index arr $
            fullSlice arr_t [DimFix $ Var ltid] -- ltid on purpose to enable hoisting.
        Kernelise.transformStms $ bodyStms $ lambdaBody lam
      let body = mkBody body_stms $ bodyResult $ lambdaBody lam
      letBind_ pat $ Op $ Out.Combine cspace (lambdaReturnType lam) mempty body
-}
    _ ->
      addStm $ soacsStmToKernels stm

bodyToKernelBody :: Out.Body lore -> KernelBody lore
bodyToKernelBody (Body attr stms res) =
  KernelBody attr stms $ map ThreadsReturn res

soacsStmToKernels :: Stm -> Out.Stm Out.Kernels
soacsStmToKernels = runIdentity . rephraseStm (injectSOACS OtherOp)

soacsLambdaToKernels :: Lambda -> Out.Lambda Out.Kernels
soacsLambdaToKernels = runIdentity . rephraseLambda (injectSOACS OtherOp)

intraGroupParalleliseBody :: (MonadFreshNames m, HasScope Out.Kernels m) =>
                             SegLevel -> Dependencies -> Names -> VName -> Body
                          -> m ([[SubExp]], [[SubExp]], Out.KernelBody Out.Kernels)
intraGroupParalleliseBody lvl deps group_variant ltid body = do
  (min_ws, avail_ws, kstms) <- runIntraGroupM (Env ltid deps group_variant) $
                 mapM_ (intraGroupStm lvl) $ bodyStms body
  return (min_ws, avail_ws,
          KernelBody () kstms $ map ThreadsReturn $ bodyResult body)
