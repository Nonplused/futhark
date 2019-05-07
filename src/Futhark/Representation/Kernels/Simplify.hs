{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
module Futhark.Representation.Kernels.Simplify
       ( simplifyKernels
       , simplifyLambda

       -- * Building blocks
       , simplifyKernelOp
       )
where

import Control.Monad
import Data.Foldable
import Data.List
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set      as S

import Futhark.Representation.Kernels
import qualified Futhark.Optimise.Simplify.Engine as Engine
import Futhark.Optimise.Simplify.Rules
import Futhark.Optimise.Simplify.Lore
import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Pass
import Futhark.Representation.SOACS.Simplify (simplifySOAC)
import qualified Futhark.Optimise.Simplify as Simplify
import Futhark.Optimise.Simplify.Rule
import qualified Futhark.Analysis.SymbolTable as ST
import qualified Futhark.Analysis.UsageTable as UT

simpleKernels :: Simplify.SimpleOps Kernels
simpleKernels = Simplify.bindableSimpleOps $ simplifyKernelOp simplifySOAC

simplifyKernels :: Prog Kernels -> PassM (Prog Kernels)
simplifyKernels =
  Simplify.simplifyProg simpleKernels kernelRules Simplify.noExtraHoistBlockers

simplifyLambda :: (HasScope Kernels m, MonadFreshNames m) =>
                  Lambda Kernels -> [Maybe VName] -> m (Lambda Kernels)
simplifyLambda =
  Simplify.simplifyLambda simpleKernels kernelRules Engine.noExtraHoistBlockers

simplifyKernelOp :: (Engine.SimplifiableLore lore,
                     BodyAttr lore ~ ()) =>
                    Simplify.SimplifyOp lore op
                 -> HostOp lore op
                 -> Engine.SimpleM lore (HostOp (Wise lore) (OpWithWisdom op), Stms (Wise lore))

simplifyKernelOp f (OtherOp op) = do
  (op', stms) <- f op
  return (OtherOp op', stms)

simplifyKernelOp _ (SegOp (SegMap lvl space ts kbody)) = do
  space' <- Engine.simplify space
  ts' <- mapM Engine.simplify ts

  (kbody', body_hoisted) <- hoistFromBody space kbody

  return (SegOp $ SegMap lvl space' ts' kbody',
          body_hoisted)

simplifyKernelOp _ (SegOp (SegRed lvl space comm red_op nes ts kbody)) = do
  (space', red_op', nes', ts', kbody', hoisted) <-
    simplifyRedOrScan space red_op nes ts kbody

  return (SegOp $ SegRed lvl space' comm red_op' nes' ts' kbody',
          hoisted)

simplifyKernelOp _ (SegOp (SegScan lvl space scan_op nes ts kbody)) = do
  (space', scan_op', nes', ts', kbody', hoisted) <-
    simplifyRedOrScan space scan_op nes ts kbody

  return (SegOp $ SegScan lvl space' scan_op' nes' ts' kbody',
          hoisted)

simplifyKernelOp _ (SegOp (SegGenRed lvl space ops ts kbody)) = do
  space' <- Engine.simplify space
  ts' <- mapM Engine.simplify ts

  (ops', ops_hoisted) <- fmap unzip $ forM ops $
    \(GenReduceOp w arrs nes dims lam) -> do
      w' <- Engine.simplify w
      arrs' <- Engine.simplify arrs
      nes' <- Engine.simplify nes
      dims' <- Engine.simplify dims
      (lam', op_hoisted) <-
        Engine.localVtable (<>scope_vtable) $
        Engine.simplifyLambda lam $
        replicate (length nes * 2) Nothing
      return (GenReduceOp w' arrs' nes' dims' lam',
              op_hoisted)

  (kbody', body_hoisted) <- hoistFromBody space kbody

  return (SegOp $ SegGenRed lvl space' ops' ts' kbody',
          mconcat ops_hoisted <> body_hoisted)

  where scope = scopeOfSegSpace space
        scope_vtable = ST.fromScope scope

simplifyKernelOp _ (SplitSpace o w i elems_per_thread) =
  (,) <$> (SplitSpace <$> Engine.simplify o <*> Engine.simplify w
           <*> Engine.simplify i <*> Engine.simplify elems_per_thread)
      <*> pure mempty
simplifyKernelOp _ (GetSize key size_class) =
  return (GetSize key size_class, mempty)
simplifyKernelOp _ (GetSizeMax size_class) =
  return (GetSizeMax size_class, mempty)
simplifyKernelOp _ (CmpSizeLe key size_class x) = do
  x' <- Engine.simplify x
  return (CmpSizeLe key size_class x', mempty)

simplifyRedOrScan :: (Engine.SimplifiableLore lore, BodyAttr lore ~ ()) =>
                     SegSpace
                  -> Lambda lore -> [SubExp] -> [Type]
                  -> KernelBody lore
                  -> Simplify.SimpleM lore
                  (SegSpace, Lambda (Wise lore), [SubExp], [Type], KernelBody (Wise lore),
                   Stms (Wise lore))
simplifyRedOrScan space scan_op nes ts kbody = do
  space' <- Engine.simplify space
  nes' <- mapM Engine.simplify nes
  ts' <- mapM Engine.simplify ts

  (scan_op', scan_op_hoisted) <-
    Engine.localVtable (<>scope_vtable) $
    Engine.simplifyLambda scan_op $ replicate (length nes * 2) Nothing

  (kbody', body_hoisted) <- hoistFromBody space kbody

  return (space', scan_op', nes', ts', kbody',
          scan_op_hoisted <> body_hoisted)

  where scope = scopeOfSegSpace space
        scope_vtable = ST.fromScope scope

hoistFromBody :: (Engine.SimplifiableLore lore, BodyAttr lore ~ ()) =>
                 SegSpace -> KernelBody lore
              -> Engine.SimpleM lore (KernelBody (Wise lore), Stms (Wise lore))
hoistFromBody space (KernelBody _ stms res) = do
  par_blocker <- Engine.asksEngineEnv $ Engine.blockHoistPar . Engine.envHoistBlockers

  ((body_stms, body_res), hoisted) <-
    Engine.localVtable (<>scope_vtable) $
    Engine.localVtable (\vtable -> vtable { ST.simplifyMemory = True }) $
    Engine.blockIf (Engine.hasFree bound_here
                    `Engine.orIf` Engine.isOp
                    `Engine.orIf` par_blocker
                    `Engine.orIf` Engine.isConsumed) $
    Engine.simplifyStms stms $ do
    res' <- mapM Engine.simplify res
    return ((res', UT.usages $ freeIn res'), mempty)

  return (mkWiseKernelBody () body_stms body_res,
          hoisted)

  where scope_vtable = ST.fromScope $ scopeOfSegSpace space
        bound_here = S.fromList $ M.keys $ scopeOfSegSpace space

mkWiseKernelBody :: (Attributes lore, CanBeWise (Op lore)) =>
                    BodyAttr lore -> Stms (Wise lore) -> [KernelResult] -> KernelBody (Wise lore)
mkWiseKernelBody attr bnds res =
  let Body attr' _ _ = mkWiseBody attr bnds res_vs
  in KernelBody attr' bnds res
  where res_vs = map kernelResultSubExp res

instance Engine.Simplifiable SplitOrdering where
  simplify SplitContiguous =
    return SplitContiguous
  simplify (SplitStrided stride) =
    SplitStrided <$> Engine.simplify stride

instance Engine.Simplifiable SegSpace where
  simplify (SegSpace phys dims) =
    SegSpace phys <$> mapM (traverse Engine.simplify) dims

instance Engine.Simplifiable KernelResult where
  simplify (ThreadsReturn what) =
    ThreadsReturn <$> Engine.simplify what
  simplify (WriteReturn ws a res) =
    WriteReturn <$> Engine.simplify ws <*> Engine.simplify a <*> Engine.simplify res
  simplify (ConcatReturns o w pte moffset what) =
    ConcatReturns
    <$> Engine.simplify o
    <*> Engine.simplify w
    <*> Engine.simplify pte
    <*> Engine.simplify moffset
    <*> Engine.simplify what

instance BinderOps (Wise Kernels) where
  mkExpAttrB = bindableMkExpAttrB
  mkBodyB = bindableMkBodyB
  mkLetNamesB = bindableMkLetNamesB

kernelRules :: RuleBook (Wise Kernels)
kernelRules = standardRules <>
              ruleBook [RuleOp removeInvariantKernelResults]
                       [RuleOp distributeKernelResults,
                        RuleBasicOp removeUnnecessaryCopy]

-- If a kernel produces something invariant to the kernel, turn it
-- into a replicate.
removeInvariantKernelResults :: TopDownRuleOp (Wise Kernels)
removeInvariantKernelResults vtable (Pattern [] kpes) attr
                             (SegOp (SegMap lvl space ts (KernelBody _ kstms kres))) = do
  (ts', kpes', kres') <-
    unzip3 <$> filterM checkForInvarianceResult (zip3 ts kpes kres)

  -- Check if we did anything at all.
  when (kres == kres')
    cannotSimplify

  addStm $ Let (Pattern [] kpes') attr $ Op $ SegOp $ SegMap lvl space ts' $
    mkWiseKernelBody () kstms kres'
  where isInvariant Constant{} = True
        isInvariant (Var v) = isJust $ ST.lookup v vtable

        checkForInvarianceResult (_, pe, ThreadsReturn se)
          | isInvariant se = do
              letBindNames_ [patElemName pe] $
                BasicOp $ Replicate (Shape $ segSpaceDims space) se
              return False
        checkForInvarianceResult _ =
          return True
removeInvariantKernelResults _ _ _ _ = cannotSimplify

-- Some kernel results can be moved outside the kernel, which can
-- simplify further analysis.
distributeKernelResults :: BottomUpRuleOp (Wise Kernels)
distributeKernelResults (vtable, used)
  (Pattern [] kpes) attr (SegOp (SegMap lvl space kts (KernelBody _ kstms kres))) = do
  -- Iterate through the bindings.  For each, we check whether it is
  -- in kres and can be moved outside.  If so, we remove it from kres
  -- and kpes and make it a binding outside.
  (kpes', kts', kres', kstms_rev) <- localScope (scopeOfSegSpace space) $
    foldM distribute (kpes, kts, kres, []) kstms

  when (kpes' == kpes)
    cannotSimplify

  addStm $ Let (Pattern [] kpes') attr $ Op $ SegOp $
    SegMap lvl space kts' $ mkWiseKernelBody () (stmsFromList $ reverse kstms_rev) kres'
  where
    free_in_kstms = fold $ fmap freeInStm kstms

    distribute (kpes', kts', kres', kstms_rev) bnd
      | Let (Pattern [] [pe]) _ (BasicOp (Index arr slice)) <- bnd,
        space_slice <- map (DimFix . Var . fst) $ unSegSpace space,
        space_slice `isPrefixOf` slice,
        remaining_slice <- drop (length space_slice) slice,
        all (isJust . flip ST.lookup vtable) $ S.toList $
          freeIn arr <> freeIn remaining_slice,
        Just (kpe, kpes'', kts'', kres'') <- isResult kpes' kts' kres' pe = do
          let outer_slice = map (\d -> DimSlice
                                       (constant (0::Int32))
                                       d
                                       (constant (1::Int32))) $
                            segSpaceDims space
              index kpe' = letBind_ (Pattern [] [kpe']) $ BasicOp $ Index arr $
                           outer_slice <> remaining_slice
          if patElemName kpe `UT.isConsumed` used
            then do precopy <- newVName $ baseString (patElemName kpe) <> "_precopy"
                    index kpe { patElemName = precopy }
                    letBind_ (Pattern [] [kpe]) $ BasicOp $ Copy precopy
            else index kpe
          return (kpes'', kts'', kres'',
                  if patElemName pe `S.member` free_in_kstms
                  then bnd : kstms_rev
                  else kstms_rev)

    distribute (kpes', kts', kres', kstms_rev) bnd =
      return (kpes', kts', kres', bnd : kstms_rev)

    isResult kpes' kts' kres' pe =
      case partition matches $ zip3 kpes' kts' kres' of
        ([(kpe,_,_)], kpes_and_kres)
          | (kpes'', kts'', kres'') <- unzip3 kpes_and_kres ->
              Just (kpe, kpes'', kts'', kres'')
        _ -> Nothing
      where matches (_, _, kre) = kre == ThreadsReturn (Var $ patElemName pe)
distributeKernelResults _ _ _ _ = cannotSimplify
