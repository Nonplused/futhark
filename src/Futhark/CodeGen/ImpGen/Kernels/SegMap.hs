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

compileSegMap pat (SegThread num_groups group_size) space kbody = do
  let (is, dims) = unzip $ unSegSpace space
  dims' <- mapM toExp dims

  num_groups' <- traverse toExp num_groups
  group_size' <- traverse toExp group_size

  sKernelThread "segmap" num_groups' group_size' (segFlat space) $ \constants -> do
    zipWithM_ dPrimV_ is $ unflattenIndex dims' $ Imp.vi32 $ segFlat space
    sWhen (isActive $ unSegSpace space) $
      compileStms mempty (kernelBodyStms kbody) $
      zipWithM_ (compileKernelResult space constants) (patternElements pat) $
      kernelBodyResult kbody
{-
compileSegMap pat (SegGroup num_groups group_size) space kbody = do
  (constants, setConstants) <- initSegMap num_groups group_size space

  sKernelGroup constants "segmap" (Just $ segFlat space) $ do
    setConstants $ kernelGroupId constants
    compileStms mempty (kernelBodyStms kbody) $
      zipWithM_ (compileKernelResult space constants) (patternElements pat) $
      kernelBodyResult kbody
-}
