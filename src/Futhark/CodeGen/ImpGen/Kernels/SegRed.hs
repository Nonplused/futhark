{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
-- | We generate code for non-segmented/single-segment SegRed using
-- the basic approach outlined in the paper "Design and GPGPU
-- Performance of Futhark’s Redomap Construct" (ARRAY '16).  The main
-- deviations are:
--
-- * While we still use two-phase reduction, we use only a single
--   kernel, with the final workgroup to write a result (tracked via
--   an atomic counter) performing the final reduction as well.
--
-- * Instead of depending on storage layout transformations to handle
--   non-commutative reductions efficiently, we slide a
--   'groupsize'-sized window over the input, and perform a parallel
--   reduction for each window.  This sacrifices the notion of
--   efficient sequentialisation, but is sometimes faster and
--   definitely simpler and more predictable (and uses less auxiliary
--   storage).
--
-- For segmented reductions we use the approach from "Strategies for
-- Regular Segmented Reductions on GPU" (FHPC '17).  This involves
-- having two different strategies, and dynamically deciding which one
-- to use based on the number of segments and segment size. We use the
-- (static) @group_size@ to decide which of the following two
-- strategies to choose:
--
-- * Large: uses one or more groups to process a single segment. If
--   multiple groups are used per segment, the intermediate reduction
--   results must be recursively reduced, until there is only a single
--   value per segment.
--
--   Each thread /can/ read multiple elements, which will greatly
--   increase performance; however, if the reduction is
--   non-commutative we will have to use a less efficient traversal
--   (with interim group-wide reductions) to enable coalesced memory
--   accesses, just as in the non-segmented case.
--
-- * Small: is used to let each group process *multiple* segments
--   within a group. We will only use this approach when we can
--   process at least two segments within a single group. In those
--   cases, we would allocate a /whole/ group per segment with the
--   large strategy, but at most 50% of the threads in the group would
--   have any element to read, which becomes highly inefficient.
module Futhark.CodeGen.ImpGen.Kernels.SegRed
  ( compileSegRed
  , compileSegRed'
  )
  where

import Control.Monad.Except
import Data.Maybe
import Data.List

import Prelude hiding (quot, rem)

import Futhark.MonadFreshNames
import Futhark.Transform.Rename
import Futhark.Representation.ExplicitMemory
import qualified Futhark.CodeGen.ImpCode.Kernels as Imp
import Futhark.CodeGen.ImpGen
import Futhark.CodeGen.ImpGen.Kernels.Base
import qualified Futhark.Representation.ExplicitMemory.IndexFunction as IxFun
import Futhark.Util.IntegralExp (quotRoundingUp, quot, rem)

type DoSegBody = (KernelConstants -> [(VName, [Imp.Exp])] -> InKernelGen ())

-- | Compile 'SegRed' instance to host-level code with calls to
-- various kernels.
compileSegRed :: Pattern ExplicitMemory
              -> SegLevel -> SegSpace
              -> Commutativity -> Lambda ExplicitMemory -> [SubExp]
              -> KernelBody ExplicitMemory
              -> CallKernelGen ()
compileSegRed pat lvl space comm red_op nes body =
  compileSegRed' pat lvl space comm red_op nes $ \constants red_dests ->
  compileStms mempty (kernelBodyStms body) $ do
  let (red_res, map_res) = splitAt (length nes) $ kernelBodyResult body

  sComment "save results to be reduced" $
    forM_ (zip red_dests red_res) $ \((d,is), res) ->
    copyDWIM d is (kernelResultSubExp res) []

  sComment "save map-out results" $ do
    let map_arrs = drop (length nes) $ patternElements pat
    zipWithM_ (compileThreadResult space constants) map_arrs map_res

-- | Like 'compileSegRed', but where the body is a monadic action.
compileSegRed' :: Pattern ExplicitMemory
               -> SegLevel -> SegSpace
               -> Commutativity -> Lambda ExplicitMemory -> [SubExp]
               -> DoSegBody
               -> CallKernelGen ()
compileSegRed' pat lvl space comm red_op nes body
  | [Constant (IntValue (Int32Value 1)), _] <- segSpaceDims space =
      nonsegmentedReduction pat num_groups group_size space comm red_op nes body
  | otherwise = do
      group_size' <- toExp $ unCount group_size
      segment_size <- toExp $ last $ segSpaceDims space
      let use_small_segments = segment_size * 2 .<. group_size'
      sIf use_small_segments
        (smallSegmentsReduction pat num_groups group_size space red_op nes body)
        (largeSegmentsReduction pat num_groups group_size space comm red_op nes body)
  where num_groups = segNumGroups lvl
        group_size = segGroupSize lvl

-- | Prepare intermediate arrays for the reduction.  Prim-typed
-- arguments go in local memory (so we need to do the allocation of
-- those arrays inside the kernel), while array-typed arguments go in
-- global memory.  Allocations for the former have already been
-- performed.  This policy is baked into how the allocations are done
-- in ExplicitAllocator.
intermediateArrays :: Count GroupSize SubExp -> SubExp
                   -> Lambda ExplicitMemory
                   -> InKernelGen [VName]
intermediateArrays (Count group_size) num_threads red_op = do
  let red_op_params = lambdaParams red_op
      (red_acc_params, _) = splitAt (length red_op_params `div` 2) red_op_params
  forM red_acc_params $ \p ->
    case paramAttr p of
      MemArray pt shape _ (ArrayIn mem _) -> do
        let shape' = Shape [num_threads] <> shape
        sArray "red_arr" pt shape' $
          ArrayIn mem $ IxFun.iota $ map (primExpFromSubExp int32) $ shapeDims shape'
      _ -> do
        let pt = elemType $ paramType p
            shape = Shape [group_size]
        sAllocArray "red_arr" pt shape $ Space "local"

nonsegmentedReduction :: Pattern ExplicitMemory
                      -> Count NumGroups SubExp -> Count GroupSize SubExp -> SegSpace
                      -> Commutativity -> Lambda ExplicitMemory -> [SubExp]
                      -> DoSegBody
                      -> CallKernelGen ()
nonsegmentedReduction segred_pat num_groups group_size space comm red_op nes body = do
  let (gtids, dims) = unzip $ unSegSpace space
  dims' <- mapM toExp dims

  num_groups' <- traverse toExp num_groups
  group_size' <- traverse toExp group_size

  let global_tid = Imp.vi32 $ segFlat space
      w = last dims'

  counter <-
    sStaticArray "counter" (Space "device") int32 $
    Imp.ArrayValues $ replicate 1 $ IntValue $ Int32Value 0

  group_res_arrs <- forM (lambdaReturnType red_op) $ \t -> do
    let pt = elemType t
        shape = Shape [unCount num_groups] <> arrayShape t
    sAllocArray "group_res_arr" pt shape $ Space "device"

  num_threads <- dPrimV "num_threads" $ unCount num_groups' * unCount group_size'

  sKernelThread "segred_nonseg" num_groups' group_size' (segFlat space) $ \constants -> do
    red_arrs <- intermediateArrays group_size (Var num_threads) red_op
    sync_arr <- sAllocArray "sync_arr" Bool (Shape [intConst Int32 1]) $ Space "local"

    -- Since this is the nonsegmented case, all outer segment IDs must
    -- necessarily be 0.
    forM_ gtids $ \v -> dPrimV_ v 0

    let num_elements = Imp.elements w
    let elems_per_thread = num_elements `quotRoundingUp` Imp.elements (kernelNumThreads constants)

    (group_result_params, red_op_renamed) <-
      reductionStageOne constants (zip gtids dims') num_elements
      global_tid elems_per_thread num_threads
      comm red_op nes red_arrs body

    let red_acc_params = take (length nes) $ lambdaParams red_op
    reductionStageTwo constants segred_pat (kernelGroupId constants) 0 [0] 0
      (kernelNumGroups constants) group_result_params red_acc_params red_op_renamed nes
      1 counter sync_arr group_res_arrs red_arrs

smallSegmentsReduction :: Pattern ExplicitMemory
                       -> Count NumGroups SubExp -> Count GroupSize SubExp
                       -> SegSpace
                       -> Lambda ExplicitMemory -> [SubExp]
                       -> DoSegBody
                       -> CallKernelGen ()
smallSegmentsReduction (Pattern _ segred_pes) num_groups group_size space red_op nes body = do
  let (gtids, dims) = unzip $ unSegSpace space
  dims' <- mapM toExp dims

  let segment_size = last dims'
  -- Careful to avoid division by zero now.
  segment_size_nonzero_v <- dPrimV "segment_size_nonzero" $
                            BinOpExp (SMax Int32) 1 segment_size

  num_groups' <- traverse toExp num_groups
  group_size' <- traverse toExp group_size
  num_threads <- dPrimV "num_threads" $ unCount num_groups' * unCount group_size'
  let segment_size_nonzero = Imp.var segment_size_nonzero_v int32
      num_segments = product $ init dims'
      segments_per_group = unCount group_size' `quot` segment_size_nonzero
      required_groups = num_segments `quotRoundingUp` segments_per_group

  emit $ Imp.DebugPrint "\n# SegRed-small" Nothing
  emit $ Imp.DebugPrint "num_segments" $ Just (int32, num_segments)
  emit $ Imp.DebugPrint "segment_size" $ Just (int32, segment_size)
  emit $ Imp.DebugPrint "segments_per_group" $ Just (int32, segments_per_group)
  emit $ Imp.DebugPrint "required_groups" $ Just (int32, required_groups)

  sKernelThread "segred_small" num_groups' group_size' (segFlat space) $ \constants -> do

    red_arrs <- intermediateArrays group_size (Var num_threads) red_op

    -- We probably do not have enough actual workgroups to cover the
    -- entire iteration space.  Some groups thus have to perform double
    -- duty; we put an outer loop to accomplish this.
    virtualiseGroups constants required_groups $ \group_id_var' -> do
      let group_id' = Imp.vi32 group_id_var'
      -- Compute the 'n' input indices.  The outer 'n-1' correspond to
      -- the segment ID, and are computed from the group id.  The inner
      -- is computed from the local thread id, and may be out-of-bounds.
      let ltid = kernelLocalThreadId constants
          segment_index = (ltid `quot` segment_size_nonzero) + (group_id' * segments_per_group)
          index_within_segment = ltid `rem` segment_size

      zipWithM_ dPrimV_ (init gtids) $ unflattenIndex (init dims') segment_index
      dPrimV_ (last gtids) index_within_segment

      let toLocalMemory ses =
            forM_ (zip red_arrs ses) $ \(arr, se) ->
            copyDWIM arr [ltid] se []

          in_bounds = body constants $ zip red_arrs $ repeat [ltid]

      sComment "apply map function if in bounds" $
        sIf (segment_size .>. 0 .&&.
             isActive (init $ zip gtids dims) .&&.
             ltid .<. segment_size * segments_per_group) in_bounds (toLocalMemory nes)

      sOp Imp.LocalBarrier

      let crossesSegment from to = (to-from) .>. (to `rem` segment_size)
      sWhen (segment_size .>. 0) $
        sComment "perform segmented scan to imitate reduction" $
        groupScan constants (Just crossesSegment) (segment_size*segments_per_group) red_op red_arrs

      sOp Imp.LocalBarrier

      sComment "save final values of segments" $
        sWhen (group_id' * segments_per_group + ltid .<. num_segments .&&.
               ltid .<. segments_per_group) $
        forM_ (zip segred_pes red_arrs) $ \(pe, arr) -> do
        -- Figure out which segment result this thread should write...
        let flat_segment_index = group_id' * segments_per_group + ltid
            gtids' = unflattenIndex (init dims') flat_segment_index
        copyDWIM (patElemName pe) gtids'
                        (Var arr) [(ltid+1) * segment_size_nonzero - 1]

      -- Finally another barrier, because we will be writing to the
      -- local memory array first thing in the next iteration.
      sOp Imp.LocalBarrier

largeSegmentsReduction :: Pattern ExplicitMemory
                       -> Count NumGroups SubExp -> Count GroupSize SubExp
                       -> SegSpace
                       -> Commutativity -> Lambda ExplicitMemory -> [SubExp]
                       -> DoSegBody
                       -> CallKernelGen ()
largeSegmentsReduction segred_pat num_groups group_size space comm red_op nes body = do
  let (gtids, dims) = unzip $ unSegSpace space
  dims' <- mapM toExp dims
  let segment_size = last dims'
      num_segments = product $ init dims'

  num_groups' <- traverse toExp num_groups
  group_size' <- traverse toExp group_size

  let (groups_per_segment, elems_per_thread) =
        groupsPerSegmentAndElementsPerThread segment_size num_segments
        num_groups' group_size'
  virt_num_groups <- dPrimV "vit_num_groups" $
    groups_per_segment * num_segments

  num_threads <- dPrimV "num_threads" $ unCount num_groups' * unCount group_size'

  threads_per_segment <- dPrimV "thread_per_segment" $
    groups_per_segment * unCount group_size'

  emit $ Imp.DebugPrint "\n# SegRed-large" Nothing
  emit $ Imp.DebugPrint "num_segments" $ Just (int32, num_segments)
  emit $ Imp.DebugPrint "segment_size" $ Just (int32, segment_size)
  emit $ Imp.DebugPrint "virt_num_groups" $ Just (int32, Imp.vi32 virt_num_groups)
  emit $ Imp.DebugPrint "num_groups" $ Just (int32, Imp.unCount num_groups')
  emit $ Imp.DebugPrint "group_size" $ Just (int32, Imp.unCount group_size')
  emit $ Imp.DebugPrint "elems_per_thread" $ Just (int32, Imp.unCount elems_per_thread)
  emit $ Imp.DebugPrint "groups_per_segment" $ Just (int32, groups_per_segment)

  group_res_arrs <- forM (lambdaReturnType red_op) $ \t -> do
    let pt = elemType t
        shape = Shape [Var virt_num_groups] <> arrayShape t
    sAllocArray "group_res_arr" pt shape $ Space "device"

  -- In principle we should have a counter for every segment.  Since
  -- the number of segments is a dynamic quantity, we would have to
  -- allocate and zero out an array here, which is expensive.
  -- However, we exploit the fact that the number of segments being
  -- reduced at any point in time is limited by the number of
  -- workgroups. If we bound the number of workgroups, we can get away
  -- with using that many counters.  FIXME: Is this limit checked
  -- anywhere?  There are other places in the compiler that will fail
  -- if the group count exceeds the maximum group size, which is at
  -- most 1024 anyway.
  let num_counters = 1024
  counter <-
    sStaticArray "counter" (Space "device") int32 $
    Imp.ArrayZeros num_counters

  sKernelThread "segred_large" num_groups' group_size' (segFlat space) $ \constants -> do

    let red_acc_params = take (length nes) $ lambdaParams red_op
    red_arrs <- intermediateArrays group_size (Var num_threads) red_op
    sync_arr <- sAllocArray "sync_arr" Bool (Shape [intConst Int32 1]) $ Space "local"

    -- We probably do not have enough actual workgroups to cover the
    -- entire iteration space.  Some groups thus have to perform double
    -- duty; we put an outer loop to accomplish this.
    virtualiseGroups constants (Imp.vi32 virt_num_groups) $ \group_id_var -> do
      let segment_gtids = init gtids
          group_id = Imp.vi32 group_id_var
          flat_segment_id = group_id `quot` groups_per_segment
          local_tid = kernelLocalThreadId constants

          global_tid = (group_id * unCount group_size' + local_tid)
                       `rem` (unCount group_size' * groups_per_segment)
          w = last dims
          first_group_for_segment = flat_segment_id * groups_per_segment

      zipWithM_ dPrimV_ segment_gtids $ unflattenIndex (init dims') flat_segment_id
      dPrim_ (last gtids) int32
      num_elements <- Imp.elements <$> toExp w

      (group_result_params, red_op_renamed) <-
        reductionStageOne constants (zip gtids dims') num_elements
        global_tid elems_per_thread threads_per_segment
        comm red_op nes red_arrs body

      let multiple_groups_per_segment =
            reductionStageTwo constants segred_pat
            group_id flat_segment_id (map (`Imp.var` int32) segment_gtids)
            first_group_for_segment groups_per_segment
            group_result_params red_acc_params red_op_renamed
            nes (fromIntegral num_counters) counter sync_arr group_res_arrs red_arrs

          one_group_per_segment =
            comment "first thread in group saves final result to memory" $
            sWhen (local_tid .==. 0) $
              forM_ (take (length nes) $ zip (patternNames segred_pat) group_result_params) $ \(v, p) ->
              copyDWIM v (map (`Imp.var` int32) segment_gtids) (Var $ paramName p) []

      sIf (groups_per_segment .==. 1) one_group_per_segment multiple_groups_per_segment

-- Careful to avoid division by zero here.  We have at least one group
-- per segment.
groupsPerSegmentAndElementsPerThread :: Imp.Exp -> Imp.Exp
                                     -> Count NumGroups Imp.Exp -> Count GroupSize Imp.Exp
                                     -> (Imp.Exp, Imp.Count Imp.Elements Imp.Exp)
groupsPerSegmentAndElementsPerThread segment_size num_segments num_groups_hint group_size =
  let groups_per_segment =
        unCount num_groups_hint `quotRoundingUp` BinOpExp (SMax Int32) 1 num_segments
      elements_per_thread =
        segment_size `quotRoundingUp` (unCount group_size * groups_per_segment)
  in (groups_per_segment, Imp.elements elements_per_thread)

reductionStageOne :: KernelConstants
                  -> [(VName, Imp.Exp)]
                  -> Imp.Count Imp.Elements Imp.Exp
                  -> Imp.Exp
                  -> Imp.Count Imp.Elements Imp.Exp
                  -> VName
                  -> Commutativity
                  -> Lambda ExplicitMemory
                  -> [SubExp]
                  -> [VName]
                  -> DoSegBody
                  -> InKernelGen ([LParam ExplicitMemory], Lambda ExplicitMemory)
reductionStageOne constants ispace num_elements global_tid elems_per_thread threads_per_segment comm red_op nes red_arrs body = do

  let red_op_params = lambdaParams red_op
      (red_acc_params, red_next_params) = splitAt (length nes) red_op_params
      (gtids, _dims) = unzip ispace
      gtid = last gtids
      local_tid = kernelLocalThreadId constants

  -- Figure out how many elements this thread should process.
  chunk_size <- dPrim "chunk_size" int32
  let ordering = case comm of Commutative -> SplitStrided $ Var threads_per_segment
                              Noncommutative -> SplitContiguous
  computeThreadChunkSize ordering global_tid elems_per_thread num_elements chunk_size

  dScope Nothing $ scopeOfLParams $ lambdaParams red_op

  forM_ (zip red_acc_params nes) $ \(p, ne) ->
    copyDWIM (paramName p) [] ne []

  red_op_renamed <- renameLambda red_op

  let doTheReduction = do
        comment "to reduce current chunk, first store our result to memory" $
          forM_ (zip red_arrs red_acc_params) $ \(arr, p) ->
          when (primType $ paramType p) $
          copyDWIM arr [local_tid] (Var $ paramName p) []

        sOp Imp.LocalBarrier

        groupReduce constants (kernelGroupSize constants) red_op_renamed red_arrs

        sOp Imp.LocalBarrier

  i <- newVName "i"
  -- If this is a non-commutative reduction, each thread must run the
  -- loop the same number of iterations, because we will be performing
  -- a group-wide reduction in there.
  let (bound, check_bounds) =
        case comm of
          Commutative -> (Imp.var chunk_size int32, id)
          Noncommutative -> (Imp.unCount elems_per_thread,
                             sWhen (Imp.var gtid int32 .<. Imp.unCount num_elements))

  sFor i Int32 bound $ do
    gtid <--
      case comm of
        Commutative ->
          global_tid +
          Imp.var threads_per_segment int32 * Imp.var i int32
        Noncommutative ->
          let index_in_segment = global_tid `quot` kernelGroupSize constants
          in local_tid +
             (index_in_segment * Imp.unCount elems_per_thread + Imp.var i int32) *
             kernelGroupSize constants

    let red_dests = zip (map paramName red_next_params) $ repeat []

    check_bounds $ sComment "apply map function" $ do
      body constants red_dests

      sComment "apply reduction operator" $
        compileBody' red_acc_params $ lambdaBody red_op

    case comm of
      Noncommutative -> do
        doTheReduction
        sComment "first thread takes carry-out; others neutral element" $ do
          let carry_out =
                forM_ (zip red_acc_params $ lambdaParams red_op_renamed) $ \(p_to, p_from) ->
                copyDWIM (paramName p_to) [] (Var $ paramName p_from) []
              reset_to_neutral =
                forM_ (zip red_acc_params nes) $ \(p, ne) ->
                copyDWIM (paramName p) [] ne []
          sIf (local_tid .==. 0) carry_out reset_to_neutral
      _ -> return ()

  group_result_params <-
    case comm of Noncommutative -> return red_acc_params
                 _              -> do doTheReduction
                                      return $ lambdaParams red_op_renamed

  return (group_result_params, red_op_renamed)

reductionStageTwo :: KernelConstants
                  -> Pattern ExplicitMemory
                  -> Imp.Exp
                  -> Imp.Exp
                  -> [Imp.Exp]
                  -> Imp.Exp
                  -> PrimExp Imp.ExpLeaf
                  -> [LParam ExplicitMemory]
                  -> [LParam ExplicitMemory]
                  -> Lambda ExplicitMemory
                  -> [SubExp]
                  -> Imp.Exp
                  -> VName
                  -> VName
                  -> [VName]
                  -> [VName]
                  -> InKernelGen ()
reductionStageTwo constants segred_pat
                  group_id flat_segment_id segment_gtids first_group_for_segment groups_per_segment
                  group_result_params red_acc_params
                  red_op_renamed nes
                  num_counters counter sync_arr group_res_arrs red_arrs = do
  let local_tid = kernelLocalThreadId constants
      group_size = kernelGroupSize constants
  old_counter <- dPrim "old_counter" int32
  (counter_mem, _, counter_offset) <- fullyIndexArray counter [flat_segment_id `rem` num_counters]
  comment "first thread in group saves group result to global memory" $
    sWhen (local_tid .==. 0) $ do
    forM_ (take (length nes) $ zip group_res_arrs group_result_params) $ \(v, p) ->
      copyDWIM v [group_id] (Var $ paramName p) []
    sOp Imp.MemFenceGlobal
    -- Increment the counter, thus stating that our result is
    -- available.
    sOp $ Imp.Atomic DefaultSpace $ Imp.AtomicAdd old_counter counter_mem counter_offset 1
    -- Now check if we were the last group to write our result.  If
    -- so, it is our responsibility to produce the final result.
    sWrite sync_arr [0] $ Imp.var old_counter int32 .==. groups_per_segment - 1

  sOp Imp.LocalBarrier

  is_last_group <- dPrim "is_last_group" Bool
  copyDWIM is_last_group [] (Var sync_arr) [0]
  sWhen (Imp.var is_last_group Bool) $ do
    -- The final group has written its result (and it was
    -- us!), so read in all the group results and perform the
    -- final stage of the reduction.  But first, we reset the
    -- counter so it is ready for next time.  This is done
    -- with an atomic to avoid warnings about write/write
    -- races in oclgrind.
    sWhen (local_tid .==. 0) $
      sOp $ Imp.Atomic DefaultSpace $ Imp.AtomicAdd old_counter counter_mem counter_offset $
      negate groups_per_segment
    comment "read in the per-group-results" $
      forM_ (zip4 red_acc_params red_arrs nes group_res_arrs) $
      \(p, arr, ne, group_res_arr) -> do
        let load_group_result =
              copyDWIM (paramName p) []
              (Var group_res_arr) [first_group_for_segment + local_tid]
            load_neutral_element =
              copyDWIM (paramName p) [] ne []
        sIf (local_tid .<. groups_per_segment)
          load_group_result load_neutral_element
        when (primType $ paramType p) $
          copyDWIM arr [local_tid] (Var $ paramName p) []

    sOp Imp.LocalBarrier

    sComment "reduce the per-group results" $ do
      groupReduce constants group_size red_op_renamed red_arrs

      sComment "and back to memory with the final result" $
        sWhen (local_tid .==. 0) $
        forM_ (take (length nes) $ zip (patternNames segred_pat) $
               lambdaParams red_op_renamed) $ \(v, p) ->
        copyDWIM v segment_gtids (Var $ paramName p) []
