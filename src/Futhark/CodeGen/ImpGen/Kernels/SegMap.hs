{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Futhark.CodeGen.ImpGen.Kernels.SegMap
  ( compileSegMap )
where

import Control.Monad.Except

import Prelude hiding (quot, rem)

import Futhark.Representation.ExplicitMemory
import Futhark.CodeGen.ImpGen.Kernels.Base
import Futhark.CodeGen.ImpGen
import qualified Futhark.CodeGen.ImpCode.Kernels as Imp

-- | Compile 'SegMap' instance code.
compileSegMap :: Pattern ExplicitMemory
              -> SegLevel
              -> SegSpace
              -> KernelBody ExplicitMemory
              -> CallKernelGen ()

compileSegMap _ SegThreadScalar{} _ _ =
  fail "compileSegMap: SegThreadScalar cannot be compiled at top level."

compileSegMap pat lvl space kbody = do
  let (is, dims) = unzip $ unSegSpace space
  dims' <- mapM toExp dims

  num_groups' <- traverse toExp $ segNumGroups lvl
  group_size' <- traverse toExp $ segGroupSize lvl

  case lvl of
    SegThreadScalar{} ->
      fail "compileSegMap: SegThreadScalar cannot be compiled at top level."

    SegThread{} ->
      sKernelThread "segmap" num_groups' group_size' (segFlat space) $ \constants -> do

      zipWithM_ dPrimV_ is $ unflattenIndex dims' $ Imp.vi32 $ segFlat space

      sWhen (isActive $ unSegSpace space) $
        compileStms mempty (kernelBodyStms kbody) $
        zipWithM_ (compileThreadResult space constants) (patternElements pat) $
        kernelBodyResult kbody

    SegGroup{} ->
      sKernelGroup "segmap" num_groups' group_size' (segFlat space) $ \constants -> do

      zipWithM_ dPrimV_ is $ unflattenIndex dims' $ Imp.vi32 $ segFlat space

      compileStms mempty (kernelBodyStms kbody) $
        zipWithM_ (compileGroupResult space constants) (patternElements pat) $
        kernelBodyResult kbody
