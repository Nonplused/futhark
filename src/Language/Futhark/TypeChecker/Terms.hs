{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, DeriveFunctor #-}
-- | Facilities for type-checking Futhark terms.  Checking a term
-- requires a little more context to track uniqueness and such.
--
-- Type inference is implemented through a variation of
-- Hindley-Milner.  The main complication is supporting the rich
-- number of built-in language constructs, as well as uniqueness
-- types.  This is mostly done in an ad hoc way, and many programs
-- will require the programmer to fall back on type annotations.
module Language.Futhark.TypeChecker.Terms
  ( checkOneExp
  , checkFunDef
  )
where
import Debug.Trace
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Control.Monad.Fail as Fail
import Data.Bitraversable
import Data.Char (isAlpha)
import Data.List
import Data.Loc
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Prelude hiding (mod)

import Language.Futhark
import Language.Futhark.Semantic (includeToString)
import Language.Futhark.Traversals
import Language.Futhark.TypeChecker.Monad hiding (BoundV, checkQualNameWithEnv)
import Language.Futhark.TypeChecker.Types hiding (checkTypeDecl)
import Language.Futhark.TypeChecker.Unify
import qualified Language.Futhark.TypeChecker.Types as Types
import qualified Language.Futhark.TypeChecker.Monad as TypeM
import Futhark.Util.Pretty hiding (space, bool)

--- Uniqueness

data Usage = Consumed SrcLoc
           | Observed SrcLoc
           deriving (Eq, Ord, Show)

type Names = S.Set VName

-- | The consumption set is a Maybe so we can distinguish whether a
-- consumption took place, but the variable went out of scope since,
-- or no consumption at all took place.
data Occurence = Occurence { observed :: Names
                           , consumed :: Maybe Names
                           , location :: SrcLoc
                           }
             deriving (Eq, Show)

instance Located Occurence where
  locOf = locOf . location

observation :: Aliasing -> SrcLoc -> Occurence
observation = flip Occurence Nothing . S.map aliasVar

consumption :: Aliasing -> SrcLoc -> Occurence
consumption = Occurence S.empty . Just . S.map aliasVar

-- | A null occurence is one that we can remove without affecting
-- anything.
nullOccurence :: Occurence -> Bool
nullOccurence occ = S.null (observed occ) && isNothing (consumed occ)

-- | A seminull occurence is one that does not contain references to
-- any variables in scope.  The big difference is that a seminull
-- occurence may denote a consumption, as long as the array that was
-- consumed is now out of scope.
seminullOccurence :: Occurence -> Bool
seminullOccurence occ = S.null (observed occ) && maybe True S.null (consumed occ)

type Occurences = [Occurence]

type UsageMap = M.Map VName [Usage]

usageMap :: Occurences -> UsageMap
usageMap = foldl comb M.empty
  where comb m (Occurence obs cons loc) =
          let m' = S.foldl' (ins $ Observed loc) m obs
          in S.foldl' (ins $ Consumed loc) m' $ fromMaybe mempty cons
        ins v m k = M.insertWith (++) k [v] m

combineOccurences :: MonadTypeChecker m => VName -> Usage -> Usage -> m Usage
combineOccurences _ (Observed loc) (Observed _) = return $ Observed loc
combineOccurences name (Consumed wloc) (Observed rloc) =
  useAfterConsume (baseName name) rloc wloc
combineOccurences name (Observed rloc) (Consumed wloc) =
  useAfterConsume (baseName name) rloc wloc
combineOccurences name (Consumed loc1) (Consumed loc2) =
  consumeAfterConsume (baseName name) (max loc1 loc2) (min loc1 loc2)

checkOccurences :: MonadTypeChecker m => Occurences -> m ()
checkOccurences = void . M.traverseWithKey comb . usageMap
  where comb _    []     = return ()
        comb name (u:us) = foldM_ (combineOccurences name) u us

allObserved :: Occurences -> Names
allObserved = S.unions . map observed

allConsumed :: Occurences -> Names
allConsumed = S.unions . map (fromMaybe mempty . consumed)

allOccuring :: Occurences -> Names
allOccuring occs = allConsumed occs <> allObserved occs

anyConsumption :: Occurences -> Maybe Occurence
anyConsumption = find (isJust . consumed)

seqOccurences :: Occurences -> Occurences -> Occurences
seqOccurences occurs1 occurs2 =
  filter (not . nullOccurence) $ map filt occurs1 ++ occurs2
  where filt occ =
          occ { observed = observed occ `S.difference` postcons }
        postcons = allConsumed occurs2

altOccurences :: Occurences -> Occurences -> Occurences
altOccurences occurs1 occurs2 =
  filter (not . nullOccurence) $ map filt1 occurs1 ++ map filt2 occurs2
  where filt1 occ =
          occ { consumed = S.difference <$> consumed occ <*> pure cons2
              , observed = observed occ `S.difference` cons2 }
        filt2 occ =
          occ { consumed = consumed occ
              , observed = observed occ `S.difference` cons1 }
        cons1 = allConsumed occurs1
        cons2 = allConsumed occurs2

--- Scope management

-- | Whether something is a global or a local variable.
data Locality = Local | Global
              deriving (Show)

data ValBinding = BoundV Locality [TypeParam] PatternType
                -- ^ Aliases in parameters indicate the lexical
                -- closure.
                | OverloadedF [PrimType] [Maybe PrimType] (Maybe PrimType)
                | EqualityF
                | OpaqueF
                | WasConsumed SrcLoc
                deriving (Show)

-- | Type checking happens with access to this environment.  The
-- tables will be extended during type-checking as bindings come into
-- scope.
data TermScope = TermScope { scopeVtable  :: M.Map VName ValBinding
                           , scopeTypeTable :: M.Map VName TypeBinding
                           , scopeNameMap :: NameMap
                           , scopeBreadCrumbs :: [BreadCrumb]
                             -- ^ Most recent first.
                           } deriving (Show)

instance Semigroup TermScope where
  TermScope vt1 tt1 nt1 bc1 <> TermScope vt2 tt2 nt2 bc2 =
    TermScope (vt2 `M.union` vt1) (tt2 `M.union` tt1) (nt2 `M.union` nt1) (bc1 <> bc2)

instance Monoid TermScope where
  mempty = TermScope mempty mempty mempty mempty

envToTermScope :: Env -> TermScope
envToTermScope env = TermScope vtable (envTypeTable env) (envNameMap env) mempty
  where vtable = M.mapWithKey valBinding $ envVtable env
        valBinding k (TypeM.BoundV tps v) =
          BoundV Global tps $ v `setAliases`
          (if arrayRank v > 0 then S.singleton (AliasBound k) else mempty)

constraintTypeVars :: Constraints -> Names
constraintTypeVars = mconcat . map f . M.elems
  where f (Constraint t _) = typeVars t
        f _ = mempty

overloadedTypeVars :: Constraints -> Names
overloadedTypeVars = mconcat . map f . M.elems
  where f (HasFields fs _) = mconcat $ map typeVars $ M.elems fs
        f _ = mempty

-- | Get the type of an expression, with all type variables
-- substituted.  Never call 'typeOf' directly (except in a few
-- carefully inspected locations)!
expType :: Exp -> TermTypeM PatternType
expType e = fmap fst $
            instantiateEmptyArrayDims (srclocOf e) Rigid <=<
            normaliseType $ typeOf e

-- | The state is a set of constraints and a counter for generating
-- type names.  This is distinct from the usual counter we use for
-- generating unique names, as these will be user-visible.
data TermTypeState = TermTypeState
                     { stateConstraints :: Constraints
                     , stateCounter :: Int
                     , stateDimTable :: M.Map (ExpBase NoInfo VName) VName
                       -- ^ Mapping function arguments encountered to
                       -- the sizes they ended up generating (when
                       -- they could not be substituted directly).
                       -- This happens for function arguments that are
                       -- not constants or names.
                     }

newtype TermTypeM a = TermTypeM (RWST
                                 TermScope
                                 Occurences
                                 TermTypeState
                                 TypeM
                                 a)
  deriving (Monad, Functor, Applicative,
            MonadReader TermScope,
            MonadWriter Occurences,
            MonadState TermTypeState,
            MonadError TypeError)

instance Fail.MonadFail TermTypeM where
  fail = typeError noLoc . ("unknown failure (likely a bug): "++)

instance MonadUnify TermTypeM where
  getConstraints = gets stateConstraints
  putConstraints x = modify $ \s -> s { stateConstraints = x }

  newTypeVar loc desc = do
    i <- incCounter
    v <- newID $ mkTypeVarName desc i
    modifyConstraints $ M.insert v $ NoConstraint Nothing loc
    return $ TypeVar mempty Nonunique (typeName v) []

  newDimVar loc rigidity name = do
    i <- incCounter
    dim <- newID $ mkTypeVarName name i
    case rigidity of
      Rigid -> modifyConstraints $ M.insert dim $ RigidSize loc
      Nonrigid -> modifyConstraints $ M.insert dim $ Size Nothing loc
    return dim

instance MonadBreadCrumbs TermTypeM where
  breadCrumb bc = local $ \env ->
    env { scopeBreadCrumbs = bc : scopeBreadCrumbs env }
  getBreadCrumbs = asks scopeBreadCrumbs

runTermTypeM :: TermTypeM a -> TypeM (a, Occurences)
runTermTypeM (TermTypeM m) = do
  initial_scope <- (initialTermScope <>) <$> (envToTermScope <$> askEnv)
  evalRWST m initial_scope $ TermTypeState mempty 0 mempty

liftTypeM :: TypeM a -> TermTypeM a
liftTypeM = TermTypeM . lift

incCounter :: TermTypeM Int
incCounter = do s <- get
                put s { stateCounter = stateCounter s + 1 }
                return $ stateCounter s

initialTermScope :: TermScope
initialTermScope = TermScope initialVtable mempty topLevelNameMap mempty
  where initialVtable = M.fromList $ mapMaybe addIntrinsicF $ M.toList intrinsics

        funF ts t = foldr (Arrow mempty Nothing . Prim) (Prim t) ts

        addIntrinsicF (name, IntrinsicMonoFun ts t) =
          Just (name, BoundV Global [] $ funF ts t)
        addIntrinsicF (name, IntrinsicOverloadedFun ts pts rts) =
          Just (name, OverloadedF ts pts rts)
        addIntrinsicF (name, IntrinsicPolyFun tvs pts rt) =
          Just (name, BoundV Global tvs $
                      fromStruct $ vacuousShapeAnnotations $
                      Arrow mempty Nothing pts' rt)
          where pts' = case pts of [pt] -> pt
                                   _    -> tupleRecord pts
        addIntrinsicF (name, IntrinsicEquality) =
          Just (name, EqualityF)
        addIntrinsicF (name, IntrinsicOpaque) =
          Just (name, OpaqueF)
        addIntrinsicF _ = Nothing

instance MonadTypeChecker TermTypeM where
  warn loc problem = liftTypeM $ warn loc problem
  newName = liftTypeM . newName
  newID = liftTypeM . newID

  checkQualName space name loc = snd <$> checkQualNameWithEnv space name loc

  bindNameMap m = local $ \scope ->
    scope { scopeNameMap = m <> scopeNameMap scope }

  localEnv env (TermTypeM m) = do
    cur_state <- get
    cur_scope <- ask
    let cur_scope' =
          cur_scope { scopeNameMap = scopeNameMap cur_scope `M.difference` envNameMap env }
    (x,new_state,occs) <- liftTypeM $ localTmpEnv env $
                          runRWST m cur_scope' cur_state
    tell occs
    put new_state
    return x

  lookupType loc qn = do
    outer_env <- liftTypeM askRootEnv
    (scope, qn'@(QualName qs name)) <- checkQualNameWithEnv Type qn loc
    case M.lookup name $ scopeTypeTable scope of
      Nothing -> undefinedType loc qn
      Just (TypeAbbr l ps def) ->
        return (qn', ps, qualifyTypeVars outer_env (map typeParamName ps) qs def, l)

  lookupMod loc name = liftTypeM $ TypeM.lookupMod loc name
  lookupMTy loc name = liftTypeM $ TypeM.lookupMTy loc name
  lookupImport loc name = liftTypeM $ TypeM.lookupImport loc name

  lookupVar loc qn = do
    outer_env <- liftTypeM askRootEnv
    (scope, qn'@(QualName qs name)) <- checkQualNameWithEnv Term qn loc

    t <- case M.lookup name $ scopeVtable scope of
      Nothing -> throwError $ TypeError loc $
                 "Unknown variable " ++ quote (pretty qn) ++ "."

      Just (WasConsumed wloc) -> useAfterConsume (baseName name) loc wloc

      Just (BoundV _ tparams t)
        | "_" `isPrefixOf` baseString name -> underscoreUse loc qn
        | otherwise -> do
            (tnames, t') <- instantiateTypeScheme loc tparams t
            let qual = qualifyTypeVars outer_env tnames qs
            t'' <- qual <$> normaliseType t'
            let msg = unwords ["instantiated", pretty qn', "to:", unwords $ map prettyName tnames, pretty t'']
            return t''

      Just OpaqueF -> do
        argtype <- newTypeVar loc "t"
        return $ Arrow mempty Nothing argtype argtype

      Just EqualityF -> do
        argtype <- newTypeVar loc "t"
        equalityType loc argtype
        return $ Arrow mempty Nothing argtype $
                 Arrow mempty Nothing argtype $ Prim Bool

      Just (OverloadedF ts pts rt) -> do
        argtype <- newTypeVar loc "t"
        mustBeOneOf ts loc argtype
        let (pts', rt') = instOverloaded argtype pts rt
        return $ fromStruct $ foldr (Arrow mempty Nothing) rt' pts'

    observe $ Ident name (Info t) loc
    return (qn', t)

      where instOverloaded argtype pts rt =
              (map (maybe (toStruct argtype) Prim) pts,
               maybe (toStruct argtype) Prim rt)

checkQualNameWithEnv :: Namespace -> QualName Name -> SrcLoc -> TermTypeM (TermScope, QualName VName)
checkQualNameWithEnv space qn@(QualName [q] _) loc
  | nameToString q == "intrinsics" = do
      -- Check if we are referring to the magical intrinsics
      -- module.
      (_, QualName _ q') <- liftTypeM $ TypeM.checkQualNameWithEnv Term (qualName q) loc
      if baseTag q' <= maxIntrinsicTag
        then checkIntrinsic space qn loc
        else checkReallyQualName space qn loc
checkQualNameWithEnv space qn@(QualName quals name) loc = do
  scope <- ask
  case quals of
    [] | Just name' <- M.lookup (space, name) $ scopeNameMap scope ->
           return (scope, name')
    _ -> checkReallyQualName space qn loc

checkIntrinsic :: Namespace -> QualName Name -> SrcLoc -> TermTypeM (TermScope, QualName VName)
checkIntrinsic space qn@(QualName _ name) loc
  | Just v <- M.lookup (space, name) intrinsicsNameMap = do
      me <- liftTypeM askImportName
      unless ("/futlib" `isPrefixOf` includeToString me) $
        warn loc "Using intrinsic functions directly can easily crash the compiler or result in wrong code generation."
      scope <- ask
      return (scope, v)
  | otherwise =
      unknownVariableError space qn loc

checkReallyQualName :: Namespace -> QualName Name -> SrcLoc -> TermTypeM (TermScope, QualName VName)
checkReallyQualName space qn loc = do
  (env, name') <- liftTypeM $ TypeM.checkQualNameWithEnv space qn loc
  return (envToTermScope env, name')

-- | Wrap 'Types.checkTypeDecl' to also perform an observation of
-- every size in the type.
checkTypeDecl :: TypeDeclBase NoInfo Name -> TermTypeM (TypeDeclBase Info VName)
checkTypeDecl tdecl = do
  (tdecl', _) <- Types.checkTypeDecl [] tdecl
  mapM_ observeDim $ nestedDims $ unInfo $ expandedType tdecl'
  return tdecl'
  where observeDim (NamedDim v) = observe $ Ident (qualLeaf v) (Info $ Prim $ Signed Int32) noLoc
        observeDim _ = return ()

-- | Instantiate a type scheme with fresh type variables for its type
-- parameters, and also any empty array dimensions in positive
-- position. Returns the names of the fresh type variables, the
-- instance list, and the instantiated type.
instantiateTypeScheme :: SrcLoc -> [TypeParam] -> PatternType
                      -> TermTypeM ([VName], PatternType)
instantiateTypeScheme loc tparams t = do
  let tnames = map typeParamName tparams
  (tparam_names, tparam_substs) <- unzip <$> mapM (instantiateTypeParam loc) tparams
  (t', anydim_names) <- instantiateMissingDims loc t
  let substs = M.fromList $ zip tnames tparam_substs
      t'' = substTypesAny (`M.lookup` substs) t'
  return (tparam_names ++ anydim_names, t'')

-- | Create a new type name and insert it (unconstrained) in the
-- substitution map.
instantiateTypeParam :: Monoid as => SrcLoc -> TypeParam -> TermTypeM (VName, Subst (TypeBase dim as))
instantiateTypeParam loc tparam = do
  i <- incCounter
  v <- newID $ mkTypeVarName (takeWhile isAlpha (baseString (typeParamName tparam))) i
  case tparam of TypeParamType x _ _ -> do
                   modifyConstraints $ M.insert v $ NoConstraint (Just x) loc
                   return (v, Subst $ TypeVar mempty Nonunique (typeName v) [])
                 TypeParamDim{} -> do
                   modifyConstraints $ M.insert v $ Size Nothing loc
                   return (v, SizeSubst $ NamedDim $ qualName v)

newArrayType :: SrcLoc -> String -> Int -> TermTypeM (StructType, StructType)
newArrayType loc desc r = do
  v <- newID $ nameFromString desc
  modifyConstraints $ M.insert v $ NoConstraint Nothing loc
  dims <- replicateM r $ newDimVar loc Nonrigid "dim"
  return (Array () Nonunique
          (ArrayPolyElem (typeName v) []) (ShapeDecl $ map (NamedDim . qualName) dims),
          TypeVar () Nonunique (typeName v) [])

--- Errors

useAfterConsume :: MonadTypeChecker m => Name -> SrcLoc -> SrcLoc -> m a
useAfterConsume name rloc wloc =
  throwError $ TypeError rloc $
  "Variable " ++ pretty name ++ " previously consumed at " ++ locStr wloc ++ ".  (Possibly through aliasing)"

consumeAfterConsume :: MonadTypeChecker m => Name -> SrcLoc -> SrcLoc -> m a
consumeAfterConsume name loc1 loc2 =
  throwError $ TypeError loc2 $
  "Variable " ++ pretty name ++ " previously consumed at " ++ locStr loc1 ++ "."

badLetWithValue :: MonadTypeChecker m => SrcLoc -> m a
badLetWithValue loc =
  throwError $ TypeError loc
  "New value for elements in let-with shares data with source array.  This is illegal, as it prevents in-place modification."

returnAliased :: MonadTypeChecker m => Name -> Name -> SrcLoc -> m ()
returnAliased fname name loc =
  throwError $ TypeError loc $
  "Unique return value of function " ++ quote (pretty fname) ++
  " is aliased to " ++ quote (pretty name) ++ ", which is not consumed."

uniqueReturnAliased :: MonadTypeChecker m => Name -> SrcLoc -> m a
uniqueReturnAliased fname loc =
  throwError $ TypeError loc $
  "A unique tuple element of return value of `" ++
  quote (pretty fname) ++ "` is aliased to some other tuple component."

--- Basic checking

matchDims :: (Monoid as, Monad m) =>
             (d -> d -> m d)
          -> TypeBase d as -> TypeBase d as
          -> m (TypeBase d as)
matchDims onDims t1 t2 =
  case (t1, t2) of
    (Array als1 u1 et1 shape1, Array als2 u2 et2 shape2) ->
      Array (als1<>als2) (min u1 u2) <$>
      matchArrayElems et1 et2 <*> onShapes shape1 shape2
    (Record f1, Record f2) ->
      Record <$> traverse (uncurry (matchDims onDims)) (M.intersectionWith (,) f1 f2)
    (TypeVar als1 u v targs1, TypeVar als2 _ _ targs2) ->
      TypeVar (als1 <> als2) u v <$> zipWithM matchTypeArg targs1 targs2
    _ -> return t1

  where matchArrayElems (ArrayPrimElem pt1) (ArrayPrimElem _) =
          return $ ArrayPrimElem pt1
        matchArrayElems (ArrayPolyElem v targs1) (ArrayPolyElem _ _targs2) =
          return $ ArrayPolyElem v targs1
        matchArrayElems (ArrayRecordElem fields1) (ArrayRecordElem fields2) =
          ArrayRecordElem <$> traverse (uncurry matchRecordArray)
          (M.intersectionWith (,) fields1 fields2)
        matchArrayElems x _ = return x

        matchRecordArray (RecordArrayElem at1) (RecordArrayElem at2) =
          RecordArrayElem <$> matchArrayElems at1 at2
        matchRecordArray (RecordArrayArrayElem at1 shape1) (RecordArrayArrayElem at2 shape2) =
          RecordArrayArrayElem <$> matchArrayElems at1 at2 <*> onShapes shape1 shape2
        matchRecordArray x _ =
          return x

        matchTypeArg ta@TypeArgType{} _ = return ta
        matchTypeArg a _ = return a

        onShapes shape1 shape2 =
          ShapeDecl <$> zipWithM onDims (shapeDims shape1) (shapeDims shape2)

-- | Replace dimension mismatches with AnyDim.  Where one of the types
-- contains an AnyDim dimension, the corresponding dimension in the
-- other type is used.
anyDimOnMismatch :: Monoid as =>
                    TypeBase (DimDecl VName) as -> TypeBase (DimDecl VName) as
                 -> (TypeBase (DimDecl VName) as, [(DimDecl VName, DimDecl VName)])
anyDimOnMismatch t1 t2 = runWriter $ matchDims onDims t1 t2
  where onDims AnyDim d2 = return d2
        onDims d1 AnyDim = return d1
        onDims d1 d2
          | d1 == d2 = return d1
          | otherwise = do tell [(d1, d2)]
                           return AnyDim

-- | Like unification, but creates new size variables where mismatches
-- occur.  Returns the new dimensions thus created.
unifyMostCommon :: SrcLoc -> PatternType -> PatternType -> TermTypeM (PatternType, [VName])
unifyMostCommon loc t1 t2 = do
  -- We are ignoring the dimensions here, because any mismatches
  -- should be turned into fresh size variables.
  unify loc (toStruct (anyDimShapeAnnotations t1))
            (toStruct (anyDimShapeAnnotations t2))
  t1' <- normaliseType t1
  t2' <- normaliseType t2
  instantiateEmptyArrayDims loc Rigid $ fst $ anyDimOnMismatch t1' t2'

-- | Determine if the types of the two expressions are identical,
-- ignoring uniqueness.  Mismatched dimensions are turned into fresh
-- type variables.  Causes a 'TypeError' if they fail to match, and
-- otherwise returns one of them.
unifyBranchTypes :: SrcLoc -> Exp -> Exp -> TermTypeM PatternType
unifyBranchTypes loc e1 e2 = do
  e1_t <- expType e1
  e2_t <- expType e2
  breadCrumb (Matching $
              "When matching the types of branches for 'if'-expression at " ++
              locStr loc ++ ".") $
    fst <$> unifyMostCommon loc e1_t e2_t

--- General binding.

data InferredType = NoneInferred
                  | Ascribed PatternType


checkPattern' :: UncheckedPattern -> InferredType
              -> TermTypeM Pattern

checkPattern' (PatternParens p loc) t =
  PatternParens <$> checkPattern' p t <*> pure loc

checkPattern' (Id name NoInfo loc) (Ascribed t) = do
  name' <- checkName Term name loc
  return $ Id name' (Info t) loc
checkPattern' (Id name NoInfo loc) NoneInferred = do
  name' <- checkName Term name loc
  t <- newTypeVar loc "t"
  return $ Id name' (Info t) loc

checkPattern' (Wildcard _ loc) (Ascribed t) =
  return $ Wildcard (Info $ t `setUniqueness` Nonunique) loc
checkPattern' (Wildcard NoInfo loc) NoneInferred = do
  t <- newTypeVar loc "t"
  return $ Wildcard (Info t) loc

checkPattern' (TuplePattern ps loc) (Ascribed t)
  | Just ts <- isTupleRecord t, length ts == length ps =
      TuplePattern <$> zipWithM checkPattern' ps (map Ascribed ts) <*> pure loc
checkPattern' p@(TuplePattern ps loc) (Ascribed t) = do
  ps_t <- replicateM (length ps) (newTypeVar loc "t")
  unify loc (tupleRecord ps_t) $ toStruct t
  t' <- normaliseType t
  checkPattern' p $ Ascribed t'
checkPattern' (TuplePattern ps loc) NoneInferred =
  TuplePattern <$> mapM (`checkPattern'` NoneInferred) ps <*> pure loc

checkPattern' (RecordPattern p_fs loc) (Ascribed (Record t_fs))
  | sort (map fst p_fs) == sort (M.keys t_fs) =
    RecordPattern . M.toList <$> check <*> pure loc
    where check = traverse (uncurry checkPattern') $ M.intersectionWith (,)
                  (M.fromList p_fs) (fmap Ascribed t_fs)
checkPattern' p@(RecordPattern fields loc) (Ascribed t) = do
  fields' <- traverse (const $ newTypeVar loc "t") $ M.fromList fields

  when (sort (M.keys fields') /= sort (map fst fields)) $
    typeError loc $ "Duplicate fields in record pattern " ++ pretty p

  unify loc (Record fields') $ toStruct t
  t' <- normaliseType t
  checkPattern' p $ Ascribed t'
checkPattern' (RecordPattern fs loc) NoneInferred =
  RecordPattern . M.toList <$> traverse (`checkPattern'` NoneInferred) (M.fromList fs) <*> pure loc

checkPattern' (PatternAscription p (TypeDecl t NoInfo) loc) maybe_outer_t = do
  (t', st_nodims, _) <- checkTypeExp t
  (st, _) <- instantiateEmptyArrayDims loc Nonrigid st_nodims

  let st' = fromStruct st
  case maybe_outer_t of
    Ascribed outer_t -> do
      unify loc (toStruct st) (toStruct outer_t)

      -- We also have to make sure that uniqueness matches.  This is
      -- done explicitly, because it is ignored by unification.
      st'' <- normaliseType st'
      outer_t' <- normaliseType outer_t
      case unifyTypesU unifyUniqueness st'' outer_t' of
        Just outer_t'' ->
          PatternAscription <$> checkPattern' p (Ascribed outer_t'') <*>
          pure (TypeDecl t' (Info st)) <*> pure loc
        Nothing ->
          typeError loc $ "Cannot match type " ++ quote (pretty outer_t') ++ " with expected type " ++
          quote (pretty st'') ++ "."

    NoneInferred ->
      PatternAscription <$> checkPattern' p (Ascribed st') <*>
      pure (TypeDecl t' (Info st)) <*> pure loc
 where unifyUniqueness u1 u2 = if u2 `subuniqueOf` u1 then Just u1 else Nothing

checkPattern' (PatternLit e NoInfo loc) (Ascribed t) = do
  e' <- checkExp e
  t' <- expType e'
  unify loc (toStruct t') (toStruct t)
  return $ PatternLit e' (Info t') loc

checkPattern' (PatternLit e NoInfo loc) NoneInferred = do
  e' <- checkExp e
  t' <- expType e'
  return $ PatternLit e' (Info t') loc

bindPatternNames :: PatternBase NoInfo Name -> TermTypeM a -> TermTypeM a
bindPatternNames = bindSpaced . map asTerm . S.toList . patternIdents
  where asTerm v = (Term, identName v)

checkPattern :: UncheckedPattern -> InferredType -> (Pattern -> TermTypeM a)
             -> TermTypeM a
checkPattern p t m = do
  checkForDuplicateNames [p]
  bindPatternNames p $
    m =<< checkPattern' p t

binding :: [Ident] -> TermTypeM a -> TermTypeM a
binding bnds = check . local (`bindVars` bnds)
  where bindVars :: TermScope -> [Ident] -> TermScope
        bindVars = foldl bindVar

        bindVar :: TermScope -> Ident -> TermScope
        bindVar scope (Ident name (Info tp) _) =
          let inedges = boundAliases $ aliases tp
              update (BoundV l tparams in_t)
              -- If 'name' is record-typed, don't alias the components
              -- to 'name', because records have no identity beyond
              -- their components.
                | Record _ <- tp = BoundV l tparams in_t
                | otherwise = BoundV l tparams (in_t `addAliases` S.insert (AliasBound name))
              update b = b

              tp' = tp `addAliases` S.insert (AliasBound name)
          in scope { scopeVtable = M.insert name (BoundV Local [] tp') $
                                   adjustSeveral update inedges $
                                   scopeVtable scope
                   }

        adjustSeveral f = flip $ foldl $ flip $ M.adjust f

        -- Check whether the bound variables have been used correctly
        -- within their scope.
        check m = do
          (a, usages) <- collectBindingsOccurences m
          checkOccurences usages

          mapM_ (checkIfUsed usages) bnds

          return a

        -- Collect and remove all occurences in @bnds@.  This relies
        -- on the fact that no variables shadow any other.
        collectBindingsOccurences m = pass $ do
          (x, usage) <- listen m
          let (relevant, rest) = split usage
          return ((x, relevant), const rest)
          where split = unzip .
                        map (\occ ->
                             let (obs1, obs2) = divide $ observed occ
                                 occ_cons = divide <$> consumed occ
                                 con1 = fst <$> occ_cons
                                 con2 = snd <$> occ_cons
                             in (occ { observed = obs1, consumed = con1 },
                                 occ { observed = obs2, consumed = con2 }))
                names = S.fromList $ map identName bnds
                divide s = (s `S.intersection` names, s `S.difference` names)

bindingTypes :: [(VName, (TypeBinding, Constraint))] -> TermTypeM a -> TermTypeM a
bindingTypes types m = do
  modifyConstraints (<>M.map snd (M.fromList types))
  local extend m
  where extend scope = scope {
          scopeTypeTable = M.map fst (M.fromList types) <> scopeTypeTable scope
          }

bindingTypeParams :: [TypeParam] -> TermTypeM a -> TermTypeM a
bindingTypeParams tparams = binding (mapMaybe typeParamIdent tparams) .
                            bindingTypes (mapMaybe typeParamType tparams)
  where typeParamType (TypeParamType l v loc) =
          Just (v, (TypeAbbr l [] (TypeVar () Nonunique (typeName v) []),
                    ParamType l loc))
        typeParamType TypeParamDim{} =
          Nothing

typeParamIdent :: TypeParam -> Maybe Ident
typeParamIdent (TypeParamDim v loc) =
  Just $ Ident v (Info (Prim (Signed Int32))) loc
typeParamIdent _ = Nothing

bindingIdent :: IdentBase NoInfo Name -> PatternType -> (Ident -> TermTypeM a)
             -> TermTypeM a
bindingIdent (Ident v NoInfo vloc) t m =
  bindSpaced [(Term, v)] $ do
    v' <- checkName Term v vloc
    let ident = Ident v' (Info t) vloc
    binding [ident] $ m ident

bindingParams :: [UncheckedTypeParam]
                    -> [UncheckedPattern]
                    -> ([TypeParam] -> [Pattern] -> TermTypeM a) -> TermTypeM a
bindingParams tps orig_ps m = do
  checkForDuplicateNames orig_ps
  checkTypeParams tps $ \tps' -> bindingTypeParams tps' $ do
    let descend ps' (p:ps) =
          checkPattern p NoneInferred $ \p' ->
            binding (S.toList $ patternIdents p') $ descend (p':ps') ps
        descend ps' [] = do
          -- Perform an observation of every type parameter.  This
          -- prevents unused-name warnings for otherwise unused
          -- dimensions.
          mapM_ observe $ mapMaybe typeParamIdent tps'
          let ps'' = reverse ps'
          checkShapeParamUses patternUses tps' ps''

          m tps' ps''

    descend [] orig_ps

bindingPattern :: PatternBase NoInfo Name -> InferredType
               -> (Pattern -> TermTypeM a) -> TermTypeM a
bindingPattern p t m = do
  checkForDuplicateNames [p]
  checkPattern p t $ \p' -> binding (S.toList $ patternIdents p') $ do
    -- Perform an observation of every declared dimension.  This
    -- prevents unused-name warnings for otherwise unused dimensions.
    mapM_ observe $ patternDims p'

    m p'

-- | Return the shapes used in a given pattern in postive and negative
-- position, respectively.
patternUses :: Pattern -> ([VName], [VName])
patternUses Id{} = mempty
patternUses Wildcard{} = mempty
patternUses PatternLit{} = mempty
patternUses (PatternParens p _) = patternUses p
patternUses (TuplePattern ps _) = foldMap patternUses ps
patternUses (RecordPattern fs _) = foldMap (patternUses . snd) fs
patternUses (PatternAscription p (TypeDecl declte _) _) =
  patternUses p <> typeExpUses declte

patternDims :: Pattern -> [Ident]
patternDims (PatternParens p _) = patternDims p
patternDims (TuplePattern pats _) = concatMap patternDims pats
patternDims (PatternAscription p (TypeDecl _ (Info t)) _) =
  patternDims p <> mapMaybe (dimIdent (srclocOf p)) (nestedDims t)
  where dimIdent _ AnyDim            = Nothing
        dimIdent _ (ConstDim _)      = Nothing
        dimIdent _ NamedDim{}        = Nothing
patternDims _ = []

sliceShape :: Monoid as =>
              SrcLoc -> [DimIndex] -> TypeBase (DimDecl VName) as
           -> TermTypeM (TypeBase (DimDecl VName) as)
sliceShape loc slice t@(Array als u et (ShapeDecl orig_dims)) =
  setDims <$> adjustDims slice orig_dims
  where setDims []    = stripArray (length orig_dims) t
        setDims dims' = Array als u et $ ShapeDecl dims'

        adjustDims (DimFix{} : idxes') (_:dims) =
          adjustDims idxes' dims
        adjustDims (DimSlice{} : idxes') (_:dims) =
          -- We create a nonrigid dimension here, because slicing will
          -- need a bounds check anyway.
          (:) <$> (NamedDim . qualName <$> newDimVar loc Nonrigid "dim") <*>
          adjustDims idxes' dims
        adjustDims _ dims =
          return dims
sliceShape _ _ t = pure t

--- Main checkers

-- | @require ts e@ causes a 'TypeError' if @expType e@ is not one of
-- the types in @ts@.  Otherwise, simply returns @e@.
require :: [PrimType] -> Exp -> TermTypeM Exp
require ts e = do mustBeOneOf ts (srclocOf e) . toStruct =<< expType e
                  return e

unifies :: StructType -> Exp -> TermTypeM Exp
unifies t e = do
  unify (srclocOf e) t =<< toStruct <$> expType e
  return e

-- The closure of a lambda or local function are those variables that
-- it references, and which local to the current top-level function.
lexicalClosure :: [Pattern] -> Occurences -> TermTypeM Aliasing
lexicalClosure params closure = do
  vtable <- asks scopeVtable
  let isLocal v = case v `M.lookup` vtable of
                    Just (BoundV Local _ _) -> True
                    _ -> False
  return $ S.map AliasBound $ S.filter isLocal $
    allOccuring closure S.\\
    S.map identName (mconcat (map patternIdents params))

checkExp :: UncheckedExp -> TermTypeM Exp

checkExp (Literal val loc) =
  return $ Literal val loc

checkExp (IntLit val NoInfo loc) = do
  t <- newTypeVar loc "t"
  mustBeOneOf anyNumberType loc t
  return $ IntLit val (Info $ fromStruct t) loc

checkExp (FloatLit val NoInfo loc) = do
  t <- newTypeVar loc "t"
  mustBeOneOf anyFloatType loc t
  return $ FloatLit val (Info $ fromStruct t) loc

checkExp (TupLit es loc) =
  TupLit <$> mapM checkExp es <*> pure loc

checkExp (RecordLit fs loc) = do
  fs' <- evalStateT (mapM checkField fs) mempty

  return $ RecordLit fs' loc
  where checkField (RecordFieldExplicit f e rloc) = do
          errIfAlreadySet f rloc
          modify $ M.insert f rloc
          RecordFieldExplicit f <$> lift (checkExp e) <*> pure rloc
        checkField (RecordFieldImplicit name NoInfo rloc) = do
          errIfAlreadySet name rloc
          (QualName _ name', t) <- lift $ lookupVar rloc $ qualName name
          modify $ M.insert name rloc
          return $ RecordFieldImplicit name' (Info t) rloc

        errIfAlreadySet f rloc = do
          maybe_sloc <- gets $ M.lookup f
          case maybe_sloc of
            Just sloc ->
              lift $ typeError rloc $ "Field '" ++ pretty f ++
              " previously defined at " ++ locStr sloc ++ "."
            Nothing -> return ()

checkExp (ArrayLit all_es _ loc) =
  -- Construct the result type and unify all elements with it.  We
  -- only create a type variable for empty arrays; otherwise we use
  -- the type of the first element.  This significantly cuts down on
  -- the number of type variables generated for pathologically large
  -- multidimensional array literals.
  case all_es of
    [] -> do et <- newTypeVar loc "t"
             t <- arrayOfM loc et (ShapeDecl [ConstDim 0]) Unique
             return $ ArrayLit [] (Info t) loc
    e:es -> do
      e' <- checkExp e
      et <- expType e'
      es' <- mapM (unifies (toStruct et) <=< checkExp) es
      et' <- normaliseType et
      t <- arrayOfM loc et' (ShapeDecl [ConstDim $ length all_es]) Unique
      return $ ArrayLit (e':es') (Info t) loc

checkExp (Range start maybe_step end NoInfo loc) = do
  start' <- require anyIntType =<< checkExp start
  start_t <- toStruct <$> expType start'
  maybe_step' <- case maybe_step of
    Nothing -> return Nothing
    Just step -> do
      let warning = warn loc "First and second element of range are identical, this will produce an empty array."
      case (start, step) of
        (Literal x _, Literal y _) -> when (x == y) warning
        (Var x_name _ _, Var y_name _ _) -> when (x_name == y_name) warning
        _ -> return ()
      Just <$> (unifies start_t =<< checkExp step)

  end' <- case end of
    DownToExclusive e -> DownToExclusive <$> (unifies start_t =<< checkExp e)
    UpToExclusive e -> UpToExclusive <$> (unifies start_t =<< checkExp e)
    ToInclusive e -> ToInclusive <$> (unifies start_t =<< checkExp e)

  -- Special case some ranges to give them a known size.
  dim <- case (isInt32 start',
               isInt32 <$> maybe_step',
               end') of
           (Just 0, Just (Just 1), UpToExclusive end'') ->
             dimFromArg end''
           (Just 0, Nothing, UpToExclusive end'') ->
             dimFromArg end''
           (Just 1, Just (Just 2), ToInclusive end'') ->
             dimFromArg end''
           _ ->
             return AnyDim

  t <- arrayOfM loc start_t (ShapeDecl [dim]) Unique

  return $ Range start' maybe_step' end' (Info (t `setAliases` mempty)) loc

checkExp (Ascript e decl NoInfo loc) = do
  decl' <- checkTypeDecl decl
  e' <- checkExp e
  t <- expType e'
  (decl_t, _) <- instantiateEmptyArrayDims loc Nonrigid $ unInfo $ expandedType decl'

  -- When type-checking the ascription, we ignore dimensions.  The
  -- intent is that they will be checked dynamically later - this is
  -- how we subvert the type system.
  unify loc (anyDimShapeAnnotations $ toStruct decl_t) (anyDimShapeAnnotations $ toStruct t)

  -- We also have to make sure that uniqueness matches.  This is done
  -- explicitly, because uniqueness is ignored by unification.
  t' <- normaliseType t
  decl_t' <- normaliseType decl_t
  unless (t' `subtypeOf` anyDimShapeAnnotations decl_t') $
    typeError loc $ "Type " ++ quote (pretty t') ++ " is not a subtype of " ++
    quote (pretty decl_t') ++ "."

  return $ Ascript e' decl' (Info (combineTypeShapes (anyDimShapeAnnotations t') $
                                   fromStruct decl_t)) loc

checkExp (BinOp op NoInfo (e1,_) (e2,_) NoInfo loc) = do
  (op', ftype) <- lookupVar loc op
  e1_arg <- checkArg e1
  e2_arg <- checkArg e2

  (p1_t, rt) <- checkApply loc ftype e1_arg
  (p2_t, rt') <- checkApply loc rt e2_arg

  return $ BinOp op' (Info ftype)
    (argExp e1_arg, Info $ toStruct p1_t) (argExp e2_arg, Info $ toStruct p2_t)
    (Info rt') loc

checkExp (Project k e NoInfo loc) = do
  e' <- checkExp e
  t <- expType e'
  kt <- mustHaveField loc k t
  return $ Project k e' (Info kt) loc

checkExp (If e1 e2 e3 _ loc) =
  sequentially checkCond $ \e1' _ -> do
  ((e2', e3'), dflow) <- tapOccurences $ checkExp e2 `alternative` checkExp e3
  brancht <- unifyBranchTypes loc e2' e3'
  let t' = addAliases brancht (`S.difference` S.map AliasBound (allConsumed dflow))
  zeroOrderType loc "returned from branch" t'
  return $ If e1' e2' e3' (Info t') loc
  where checkCond = do
          e1' <- checkExp e1
          unify (srclocOf e1') (Prim Bool) . toStruct =<< expType e1'
          return e1'

checkExp (Parens e loc) =
  Parens <$> checkExp e <*> pure loc

checkExp (QualParens modname e loc) = do
  (modname',mod) <- lookupMod loc modname
  case mod of
    ModEnv env -> localEnv (qualifyEnv modname' env) $ do
      e' <- checkExp e
      return $ QualParens modname' e' loc
    ModFun{} ->
      typeError loc $ "Module " ++ pretty modname ++ " is a parametric module."
  where qualifyEnv modname' env =
          env { envNameMap = M.map (qualify' modname') $ envNameMap env }
        qualify' modname' (QualName qs name) =
          QualName (qualQuals modname' ++ [qualLeaf modname'] ++ qs) name

checkExp (Var qn NoInfo loc) = do
  -- The qualifiers of a variable is divided into two parts: first a
  -- possibly-empty sequence of module qualifiers, followed by a
  -- possible-empty sequence of record field accesses.  We use scope
  -- information to perform the split, by taking qualifiers off the
  -- end until we find a module.

  (qn', t, fields) <- findRootVar (qualQuals qn) (qualLeaf qn)

  foldM checkField (Var qn' (Info t) loc) fields

  where findRootVar qs name =
          (whenFound <$> lookupVar loc (QualName qs name)) `catchError` notFound qs name

        whenFound (qn', t) = (qn', t, [])

        notFound qs name err
          | null qs = throwError err
          | otherwise = do
              (qn', t, fields) <- findRootVar (init qs) (last qs) `catchError`
                                  const (throwError err)
              return (qn', t, fields++[name])

        checkField e k = do
          t <- expType e
          kt <- mustHaveField loc k t
          return $ Project k e (Info kt) loc

checkExp (Negate arg loc) = do
  arg' <- require anyNumberType =<< checkExp arg
  return $ Negate arg' loc

checkExp (Apply e1 e2 NoInfo NoInfo loc) = do
  e1' <- checkExp e1
  arg <- checkArg e2
  t <- expType e1'
  (t1, rt) <- checkApply loc t arg
  return $ Apply e1' (argExp arg) (Info $ diet t1) (Info rt) loc

checkExp (LetPat pat e body NoInfo loc) =
  sequentially (checkExp e) $ \e' e_occs -> do
    -- Not technically an ascription, but we want the pattern to have
    -- exactly the type of 'e'.
    t <- expType e'
    case anyConsumption e_occs of
      Just c ->
        let msg = "of value computed with consumption at " ++ locStr (location c)
        in zeroOrderType loc msg t
      _ -> return ()
    bindingPattern pat (Ascribed t) $ \pat' -> do
      body' <- checkExp body
      body_t <- unscopeType (S.map identName $ patternIdents pat') <$> expType body'
      return $ LetPat pat' e' body' (Info body_t) loc

checkExp (LetFun name (tparams, params, maybe_retdecl, NoInfo, e) body loc) =
  sequentially (checkFunDef' (name, maybe_retdecl, tparams, params, e, loc)) $
    \(name', tparams', params', maybe_retdecl', rettype, e') closure -> do

    closure' <- lexicalClosure params' closure

    let ftype = foldr (uncurry (Arrow ()) . patternParam) rettype params'
        entry = BoundV Local tparams' $ ftype `setAliases` closure'
        bindF scope = scope { scopeVtable = M.insert name' entry $ scopeVtable scope
                            , scopeNameMap = M.insert (Term, name) (qualName name') $
                                             scopeNameMap scope }
    body' <- local bindF $ checkExp body

    return $ LetFun name' (tparams', params', maybe_retdecl', Info rettype, e') body' loc

checkExp (LetWith dest src idxes ve body NoInfo loc) =
  sequentially (checkIdent src) $ \src' _ -> do

  (t, _) <- newArrayType (srclocOf src) "src" $ length idxes
  unify loc t $ toStruct $ unInfo $ identType src'
  idxes' <- mapM checkDimIndex idxes
  elemt <- sliceShape loc idxes' =<< normaliseType t

  unless (unique $ unInfo $ identType src') $
    typeError loc $ "Source " ++ quote (pretty (identName src)) ++
    " has type " ++ pretty (unInfo $ identType src') ++ ", which is not unique."
  vtable <- asks scopeVtable
  forM_ (aliases $ unInfo $ identType src') $ \v ->
    case aliasVar v `M.lookup` vtable of
      Just (BoundV Local _ v_t)
        | not $ unique v_t ->
            typeError loc $ "Source " ++ quote (pretty (identName src)) ++
            " aliases " ++ quote (prettyName (aliasVar v)) ++ ", which is not consumable."
      _ -> return ()

  sequentially (unifies (toStruct elemt) =<< checkExp ve) $ \ve' _ -> do
    ve_t <- expType ve'
    when (AliasBound (identName src') `S.member` aliases ve_t) $
      badLetWithValue loc

    bindingIdent dest (unInfo (identType src') `setAliases` S.empty) $ \dest' -> do
      body' <- consuming src' $ checkExp body
      body_t <- unscopeType (S.singleton $ identName dest') <$> expType body'
      return $ LetWith dest' src' idxes' ve' body' (Info body_t) loc

checkExp (Update src idxes ve loc) = do
  (t, _) <- newArrayType (srclocOf src) "src" $ length idxes
  idxes' <- mapM checkDimIndex idxes
  elemt <- sliceShape loc idxes' =<< normaliseType t

  sequentially (checkExp ve >>= unifies elemt) $ \ve' _ ->
    sequentially (checkExp src >>= unifies t) $ \src' _ -> do

    src_t <- expType src'
    unless (unique src_t) $
      typeError loc $ "Source " ++ quote (pretty src) ++
      " has type " ++ pretty src_t ++ ", which is not unique"

    let src_als = aliases src_t
    ve_t <- expType ve'
    unless (S.null $ src_als `S.intersection` aliases ve_t) $ badLetWithValue loc

    consume loc src_als
    return $ Update src' idxes' ve' loc

checkExp (RecordUpdate src fields ve NoInfo loc) = do
  src' <- checkExp src
  ve' <- checkExp ve
  a <- expType src'
  r <- foldM (flip $ mustHaveField loc) a fields
  unify loc (toStruct r) . toStruct =<< expType ve'
  return $ RecordUpdate src' fields ve' (Info $ fromStruct a) loc

checkExp (Index e idxes NoInfo loc) = do
  (t, _) <- newArrayType (srclocOf e) "e" $ length idxes
  e' <- unifies t =<< checkExp e
  idxes' <- mapM checkDimIndex idxes
  t' <- sliceShape loc idxes' =<< normaliseType (typeOf e')
  return $ Index e' idxes' (Info t') loc

checkExp (Unsafe e loc) =
  Unsafe <$> checkExp e <*> pure loc

checkExp (Assert e1 e2 NoInfo loc) = do
  e1' <- require [Bool] =<< checkExp e1
  e2' <- checkExp e2
  return $ Assert e1' e2' (Info (pretty e1)) loc

checkExp (Lambda tparams params body rettype_te NoInfo loc) =
  removeSeminullOccurences $
  bindingParams tparams params $ \tparams' params' -> do
    rettype_checked <- traverse checkTypeExp rettype_te
    let declared_rettype =
          case rettype_checked of Just (_, st, _) -> Just st
                                  Nothing -> Nothing
    (body', closure) <-
      tapOccurences $ noUnique $ checkFunBody body declared_rettype loc
    body_t <- expType body'
    (rettype', rettype_st) <-
      case rettype_checked of
        Just (te, st, _) -> do
          (st', _) <- instantiateEmptyArrayDims (srclocOf te) Nonrigid st
          return (Just te, st')
        Nothing ->
          return (Nothing, inferReturnUniqueness params' body_t)

    checkGlobalAliases params' body_t loc

    closure' <- lexicalClosure params' closure
    let msg = unlines [unwords ["lambda ", pretty tparams', pretty params', pretty rettype_st]]

    return $ Lambda tparams' params' body' rettype' (Info (closure', rettype_st)) loc

checkExp (OpSection op _ loc) = do
  (op', ftype) <- lookupVar loc op
  return $ OpSection op' (Info ftype) loc

checkExp (OpSectionLeft op _ e _ _ loc) = do
  (op', ftype) <- lookupVar loc op
  e_arg <- checkArg e
  (t1, rt) <- checkApply loc ftype e_arg
  case rt of
    Arrow _ _ t2 rettype ->
      return $ OpSectionLeft op' (Info ftype) (argExp e_arg)
      (Info $ toStruct t1, Info $ toStruct t2) (Info rettype) loc
    _ -> typeError loc $
         "Operator section with invalid operator of type " ++ pretty ftype

checkExp (OpSectionRight op _ e _ _ loc) = do
  (op', ftype) <- lookupVar loc op
  e_arg <- checkArg e
  case ftype of
    Arrow as1 m1 t1 (Arrow as2 m2 t2 ret) -> do
      (t2', Arrow _ _ t1' rettype) <-
        checkApply loc (Arrow as2 m2 t2 (Arrow as1 m1 t1 ret)) e_arg
      return $ OpSectionRight op' (Info ftype) (argExp e_arg)
        (Info $ toStruct t1', Info $ toStruct t2') (Info rettype) loc
    _ -> typeError loc $
         "Operator section with invalid operator of type " ++ pretty ftype

checkExp (ProjectSection fields NoInfo loc) = do
  a <- newTypeVar loc "a"
  b <- foldM (flip $ mustHaveField loc) a fields
  return $ ProjectSection fields (Info $ Arrow mempty Nothing a b) loc

checkExp (IndexSection idxes NoInfo loc) = do
  (t, _) <- newArrayType loc "e" (length idxes)
  idxes' <- mapM checkDimIndex idxes
  let t' = stripArray (length $ filter isFix idxes) t
  return $ IndexSection idxes' (Info $ fromStruct $ Arrow mempty Nothing t t') loc
  where isFix DimFix{} = True
        isFix _        = False

checkExp (DoLoop mergepat mergeexp form loopbody loc) =
  sequentially (checkExp mergeexp) $ \mergeexp' _ -> do

  zeroOrderType (srclocOf mergeexp) "used as loop variable" (typeOf mergeexp')

  -- The handling of dimension sizes is a bit intricate, but very
  -- similar to checking a function, followed by checking a call to
  -- it.  The overall procedure is as follows:
  --
  -- (1) All empty dimensions in the merge pattern are instantiated
  -- with nonrigid size variables.  All explicitly specified
  -- dimensions are preserved.
  --
  -- (2) The body of the loop is type-checked.  The result type is
  -- combined with the merge pattern type to determine which sizes are
  -- variant, and these are set to AnyDim in the merge pattern.
  --
  -- (3) We now conceptually have a function parameter type and return
  -- type.  We check that it can be called with the initial merge
  -- values as argument.  The result of this is the type of the loop
  -- as a whole.
  --
  -- (There is also a convergence loop for inferring uniqueness, but
  -- that's orthogonal to the size handling.)that

  (merge_t, new_dims) <-
    instantiateEmptyArrayDims loc Nonrigid . -- dim handling (1)
    anyDimShapeAnnotations .
    (`setAliases` mempty) =<< expType mergeexp'

  -- dim handling (2)
  let checkLoopReturnSize mergepat' loopbody' = do
        loopbody_t <- expType loopbody'
        pat_t <- normaliseType $ patternType mergepat'
        -- We are ignoring the dimensions here, because any mismatches
        -- should be turned into fresh size variables.
        unify loc (toStruct (anyDimShapeAnnotations pat_t))
                  (toStruct (anyDimShapeAnnotations loopbody_t))
        pat_t' <- normaliseType pat_t
        loopbody_t' <- normaliseType loopbody_t

        -- For each new_dims, figure out what they are instantiated
        -- with in the initial value.  This is used to determine
        -- whether a size is invariant because it always matches the
        -- initial instantiation of that size.
        let initSubst (NamedDim v, d) = Just (v, d)
            initSubst _ = Nothing
        init_substs <- M.fromList . mapMaybe initSubst . snd .
                       anyDimOnMismatch pat_t' <$>
                       expType mergeexp'

        -- Figure out which of the 'new_dims' dimensions are
        -- variant.  This works because we know they are each only
        -- used once.
        let mismatchSubst (NamedDim v, d)
              | qualLeaf v `elem` new_dims =
                  case M.lookup v init_substs of
                    Just d' | d' == d -> Just (qualLeaf v, SizeSubst d)
                    _ -> Just (qualLeaf v, SizeSubst AnyDim)
            mismatchSubst _ = Nothing
            mismatches = M.fromList $ mapMaybe mismatchSubst $ snd $
                         anyDimOnMismatch pat_t' loopbody_t'

        return $ applySubst (`M.lookup` mismatches) mergepat'

  -- First we do a basic check of the loop body to figure out which of
  -- the merge parameters are being consumed.  For this, we first need
  -- to check the merge pattern, which requires the (initial) merge
  -- expression.
  --
  -- Play a little with occurences to ensure it does not look like
  -- none of the merge variables are being used.
  ((mergepat', form', loopbody'), bodyflow) <-
    case form of
      For i uboundexp -> do
        uboundexp' <- require anySignedType =<< checkExp uboundexp
        bound_t <- expType uboundexp'
        bindingIdent i bound_t $ \i' ->
          noUnique $ bindingPattern mergepat (Ascribed merge_t) $
          \mergepat' -> onlySelfAliasing $ tapOccurences $ do
            loopbody' <- checkExp loopbody
            mergepat'' <- checkLoopReturnSize mergepat' loopbody'
            return (mergepat'',
                    For i' uboundexp',
                    loopbody')

      ForIn xpat e -> do
        (arr_t, _) <- newArrayType (srclocOf e) "e" 1
        e' <- unifies arr_t =<< checkExp e
        t <- expType e'
        case t of
          _ | Just t' <- peelArray 1 t ->
                bindingPattern xpat (Ascribed t') $ \xpat' ->
                noUnique $ bindingPattern mergepat (Ascribed merge_t) $
                \mergepat' -> onlySelfAliasing $ tapOccurences $ do
                  loopbody' <- checkExp loopbody
                  mergepat'' <- checkLoopReturnSize mergepat' loopbody'
                  return (mergepat'',
                          ForIn xpat' e',
                          loopbody')
            | otherwise ->
                typeError (srclocOf e) $
                "Iteratee of a for-in loop must be an array, but expression has type " ++ pretty t

      While cond ->
        noUnique $ bindingPattern mergepat (Ascribed merge_t) $ \mergepat' ->
        onlySelfAliasing $ tapOccurences $
        sequentially (unifies (Prim Bool) =<< checkExp cond) $ \cond' _ -> do
          loopbody' <- checkExp loopbody
          mergepat'' <- checkLoopReturnSize mergepat' loopbody'
          return (mergepat'',
                  While cond',
                  loopbody')

  mergepat'' <- do
    loop_t <- expType loopbody'
    convergePattern mergepat' (allConsumed bodyflow) loop_t (srclocOf loopbody')

  let consumeMerge (Id _ (Info pt) ploc) mt
        | unique pt = consume ploc $ aliases mt
      consumeMerge (TuplePattern pats _) t | Just ts <- isTupleRecord t =
        zipWithM_ consumeMerge pats ts
      consumeMerge (PatternParens pat _) t =
        consumeMerge pat t
      consumeMerge (PatternAscription pat _ _) t =
        consumeMerge pat t
      consumeMerge _ _ =
        return ()
  consumeMerge mergepat'' =<< expType mergeexp'

  -- dim handling (3)
  unify loc (toStruct $ patternType mergepat'') . toStruct =<< expType mergeexp'

  return $ DoLoop mergepat'' mergeexp' form' loopbody' loc

  where
    convergePattern pat body_cons body_t body_loc = do
      let consumed_merge = S.map identName (patternIdents pat) `S.intersection`
                           body_cons
          uniquePat (Wildcard (Info t) wloc) =
            Wildcard (Info $ t `setUniqueness` Nonunique) wloc
          uniquePat (PatternParens p ploc) =
            PatternParens (uniquePat p) ploc
          uniquePat (Id name (Info t) iloc)
            | name `S.member` consumed_merge =
                let t' = t `setUniqueness` Unique `setAliases` mempty
                in Id name (Info t') iloc
            | otherwise =
                let t' = case t of Record{} -> t
                                   _        -> t `setUniqueness` Nonunique
                in Id name (Info t') iloc
          uniquePat (TuplePattern pats ploc) =
            TuplePattern (map uniquePat pats) ploc
          uniquePat (RecordPattern fs ploc) =
            RecordPattern (map (fmap uniquePat) fs) ploc
          uniquePat (PatternAscription p t ploc) =
            PatternAscription p t ploc
          uniquePat p@PatternLit{} = p

          -- Make the pattern unique where needed.
          pat' = uniquePat pat

      pat_t <- normaliseType $ patternType pat'
      unless (toStructural body_t `subtypeOf` toStructural pat_t) $
        unexpectedType body_loc (toStruct body_t) [toStruct pat_t]

      -- Check that the new values of consumed merge parameters do not
      -- alias something bound outside the loop, AND that anything
      -- returned for a unique merge parameter does not alias anything
      -- else returned.
      bound_outside <- asks $ S.fromList . M.keys . scopeVtable
      let checkMergeReturn (Id pat_v (Info pat_v_t) _) t
            | unique pat_v_t,
              v:_ <- S.toList $ S.map aliasVar (aliases t) `S.intersection` bound_outside =
                lift $ typeError loc $ "Loop return value corresponding to merge parameter " ++
                quote (prettyName pat_v) ++ " aliases " ++ prettyName v ++ "."
            | otherwise = do
                (cons,obs) <- get
                unless (S.null $ aliases t `S.intersection` cons) $
                  lift $ typeError loc $ "Loop return value for merge parameter " ++
                  quote (prettyName pat_v) ++ " aliases other consumed merge parameter."
                when (unique pat_v_t &&
                      not (S.null (aliases t `S.intersection` (cons<>obs)))) $
                  lift $ typeError loc $ "Loop return value for consuming merge parameter " ++
                  quote (prettyName pat_v) ++ " aliases previously returned value."
                if unique pat_v_t
                  then put (cons<>aliases t, obs)
                  else put (cons, obs<>aliases t)
          checkMergeReturn (PatternParens p _) t =
            checkMergeReturn p t
          checkMergeReturn (PatternAscription p _ _) t =
            checkMergeReturn p t
          checkMergeReturn (RecordPattern pfs _) (Record tfs) =
            sequence_ $ M.elems $ M.intersectionWith checkMergeReturn (M.fromList pfs) tfs
          checkMergeReturn (TuplePattern pats _) t | Just ts <- isTupleRecord t =
            zipWithM_ checkMergeReturn pats ts
          checkMergeReturn _ _ =
            return ()

      (pat_cons, _) <- execStateT (checkMergeReturn pat' body_t) (mempty, mempty)
      let body_cons' = body_cons <> S.map aliasVar pat_cons
      if body_cons' == body_cons && patternPatternType pat' == patternPatternType pat
        then return pat'
        else convergePattern pat' body_cons' body_t body_loc

checkExp (VConstr0 name NoInfo loc) = do
  t <- newTypeVar loc "t"
  mustHaveConstr loc name t
  return $ VConstr0 name (Info t) loc

checkExp (Match _ [] NoInfo loc) =
  typeError loc "Match expressions must have at least one case."

checkExp (Match e (c:cs) NoInfo loc) =
  sequentially (checkExp e) $ \e' _ -> do
    mt <- expType e'
    (cs', t) <- checkCases mt c cs
    zeroOrderType loc "returned from pattern match" t
    return $ Match e' cs' (Info t) loc

checkCases :: PatternType
           -> CaseBase NoInfo Name
           -> [CaseBase NoInfo Name]
           -> TermTypeM ([CaseBase Info VName], PatternType)
checkCases mt c [] = do
  (c', t) <- checkCase mt c
  return ([c'], t)
checkCases mt c (c2:cs) = do
  (((c', c_t), (cs', cs_t)), dflow) <-
    tapOccurences $ checkCase mt c `alternative` checkCases mt c2 cs
  unify (srclocOf c) (toStruct c_t) (toStruct cs_t)
  t <- (`addAliases` (`S.difference` S.map AliasBound (allConsumed dflow))) . fst <$>
       unifyMostCommon (srclocOf c) c_t cs_t
  return (c':cs', t)

checkCase :: PatternType -> CaseBase NoInfo Name
          -> TermTypeM (CaseBase Info VName, PatternType)
checkCase mt (CasePat p caseExp loc) =
  bindingPattern p (Ascribed mt) $ \p' -> do
    caseExp' <- checkExp caseExp
    caseType <- expType caseExp'
    return (CasePat p' caseExp' loc, caseType)

-- | An unmatched pattern. Used in in the generation of
-- unmatched pattern warnings by the type checker.
data Unmatched p = UnmatchedNum p [ExpBase Info VName]
                 | UnmatchedBool p
                 | UnmatchedEnum p
                 | Unmatched p
                 deriving (Functor, Show)

instance Pretty (Unmatched (PatternBase Info VName)) where
  ppr um = case um of
      (UnmatchedNum p nums) -> ppr' p <+> text "where p is not one of" <+> ppr nums
      (UnmatchedBool p)     -> ppr' p
      (UnmatchedEnum p)     -> ppr' p
      (Unmatched p)         -> ppr' p
    where
      ppr' (PatternAscription p t _) = ppr p <> text ":" <+> ppr t
      ppr' (PatternParens p _)       = parens $ ppr' p
      ppr' (Id v _ _)                = pprName v
      ppr' (TuplePattern pats _)     = parens $ commasep $ map ppr' pats
      ppr' (RecordPattern fs _)      = braces $ commasep $ map ppField fs
        where ppField (name, t)      = text (nameToString name) <> equals <> ppr' t
      ppr' Wildcard{}                = text "_"
      ppr' (PatternLit e _ _)        = ppr e

unpackPat :: Pattern -> [Maybe Pattern]
unpackPat Wildcard{} = [Nothing]
unpackPat (PatternParens p _) = unpackPat p
unpackPat Id{} = [Nothing]
unpackPat (TuplePattern ps _) = Just <$> ps
unpackPat (RecordPattern fs _) = Just . snd <$> sortFields (M.fromList fs)
unpackPat (PatternAscription p _ _) = unpackPat p
unpackPat p@PatternLit{} = [Just p]

wildPattern :: Pattern -> Int -> Unmatched Pattern -> Unmatched Pattern
wildPattern (TuplePattern ps loc) pos um = f <$> um
  where f p = TuplePattern (take (pos - 1) ps' ++ [p] ++ drop pos ps') loc
        ps' = map wildOut ps
        wildOut p = Wildcard (Info (patternPatternType p)) (srclocOf p)
wildPattern (RecordPattern fs loc) pos um = wildRecord <$> um
    where wildRecord p =
            RecordPattern (take (pos - 1) fs' ++ [(fst (fs!!(pos - 1)), p)] ++ drop pos fs') loc
          fs' = map wildOut fs
          wildOut (f,p) = (f, Wildcard (Info (patternPatternType p)) (srclocOf p))
wildPattern (PatternAscription p _ _) pos um = wildPattern p pos um
wildPattern (PatternParens p _) pos um = wildPattern p pos um
wildPattern _ _ um = um

checkUnmatched :: (MonadBreadCrumbs m, MonadTypeChecker m) => Exp -> m ()
checkUnmatched e = void $ checkUnmatched' e >> astMap tv e
  where checkUnmatched' (Match _ cs _ loc) =
          let ps = map (\(CasePat p _ _) -> p) cs
          in case unmatched id ps of
              []  -> return ()
              ps' -> typeError loc $ "Unmatched cases in match expression: \n"
                                     ++ unlines (map (("  " ++) . pretty) ps')
        checkUnmatched' _ = return ()
        tv = ASTMapper { mapOnExp =
                           \e' -> checkUnmatched' e' >> return e'
                       , mapOnName        = pure
                       , mapOnQualName    = pure
                       , mapOnStructType  = pure
                       , mapOnPatternType = pure
                       }

unmatched :: (Unmatched Pattern -> Unmatched Pattern) -> [Pattern] -> [Unmatched Pattern]
unmatched hole (p:ps)
  | sameStructure labeledCols = do
    (i, cols) <- labeledCols
    let hole' p' = hole $ wildPattern p i p'
    case sequence cols of
      Nothing      -> []
      Just cs
        | all isPatternLit cs  -> map hole' $ localUnmatched cs
        | otherwise            -> unmatched hole' cs

  where labeledCols = zip [1..] $ transpose $ map unpackPat (p:ps)

        localUnmatched :: [Pattern] -> [Unmatched Pattern]
        localUnmatched [] = []
        localUnmatched ps'@(p':_) =
          case patternType p'  of
            Enum cs'' ->
              let matched = nub $ mapMaybe (pExp >=> constr) ps'
              in map (UnmatchedEnum . buildEnum (Enum cs'')) $ cs'' \\ matched
            Prim t
              | not (any idOrWild ps') ->
                case t of
                  Bool ->
                    let matched = nub $ mapMaybe (pExp >=> bool) $ filter isPatternLit ps'
                    in map (UnmatchedBool . buildBool (Prim t)) $ [True, False] \\ matched
                  _ ->
                    let matched = mapMaybe pExp $ filter isPatternLit ps'
                    in [UnmatchedNum (buildId (Info (Prim t)) "p") matched]
            _ -> []

        sameStructure [] = True
        sameStructure (x:xs) = all (\y -> length y == length x' ) xs'
          where (x':xs') = map snd (x:xs)

        pExp (PatternLit e' _ _) = Just e'
        pExp _ = Nothing

        constr (VConstr0 c _ _) = Just c
        constr (Ascript e' _ _ _)  = constr e'
        constr _ = Nothing

        isPatternLit PatternLit{} = True
        isPatternLit (PatternAscription p' _ _) = isPatternLit p'
        isPatternLit (PatternParens p' _)  = isPatternLit p'
        isPatternLit _ = False

        idOrWild Id{} = True
        idOrWild Wildcard{} = True
        idOrWild (PatternAscription p' _ _) = idOrWild p'
        idOrWild (PatternParens p' _) = idOrWild p'
        idOrWild _ = False

        bool (Literal (BoolValue b) _ ) = Just b
        bool _ = Nothing

        buildEnum t c =
          PatternLit (VConstr0 c (Info t) noLoc) (Info t) noLoc
        buildBool t b =
          PatternLit (Literal (BoolValue b) noLoc) (Info (vacuousShapeAnnotations t)) noLoc
        buildId t n =
          -- The VName tag here will never be used since the value
          -- exists exclusively for printing warnings.
          Id (VName (nameFromString n) (-1)) t noLoc

unmatched _ _ = []

checkIdent :: IdentBase NoInfo Name -> TermTypeM Ident
checkIdent (Ident name _ loc) = do
  (QualName _ name', vt) <- lookupVar loc (qualName name)
  return $ Ident name' (Info vt) loc

checkDimIndex :: DimIndexBase NoInfo Name -> TermTypeM DimIndex
checkDimIndex (DimFix i) =
  DimFix <$> (unifies (Prim $ Signed Int32) =<< checkExp i)
checkDimIndex (DimSlice i j s) =
  DimSlice
  <$> maybe (return Nothing) (fmap Just . unifies (Prim $ Signed Int32) <=< checkExp) i
  <*> maybe (return Nothing) (fmap Just . unifies (Prim $ Signed Int32) <=< checkExp) j
  <*> maybe (return Nothing) (fmap Just . unifies (Prim $ Signed Int32) <=< checkExp) s

sequentially :: TermTypeM a -> (a -> Occurences -> TermTypeM b) -> TermTypeM b
sequentially m1 m2 = do
  (a, m1flow) <- collectOccurences m1
  (b, m2flow) <- collectOccurences $ m2 a m1flow
  occur $ m1flow `seqOccurences` m2flow
  return b

type Arg = (Exp, PatternType, Occurences, SrcLoc)

argExp :: Arg -> Exp
argExp (e, _, _, _) = e

argType :: Arg -> PatternType
argType (_, t, _, _) = t

checkArg :: UncheckedExp -> TermTypeM Arg
checkArg arg = do
  (arg', dflow) <- collectOccurences $ checkExp arg
  arg_t <- expType arg'
  return (arg', arg_t, dflow, srclocOf arg')

checkApply :: SrcLoc -> PatternType -> Arg
           -> TermTypeM (PatternType, PatternType)
checkApply loc funt@(Arrow as pname tp1 tp2) (argexp, argtype, dflow, argloc) = do
  unify argloc (toStruct tp1) (toStruct argtype)

  -- Perform substitutions of instantiated variables in the types.
  tp1' <- normaliseType tp1
  tp2' <- normaliseType tp2
  argtype' <- normaliseType argtype

  occur [observation as loc]

  checkOccurences dflow
  occurs <- consumeArg argloc argtype' (diet tp1')

  case anyConsumption dflow of
    Just c ->
      let msg = "of value computed with consumption at " ++ locStr (location c)
      in zeroOrderType argloc msg tp1
    _ -> return ()

  occur $ dflow `seqOccurences` occurs
  parsubst <- case pname of
                Just pname' ->
                  flip M.lookup . M.singleton pname' .
                  SizeSubst <$> sizeSubst tp1' argexp
                _ -> return $ const Nothing
  let tp2'' = applySubst parsubst $ returnType tp2' (diet tp1') argtype'
  let msg = unlines ["argument " ++ pretty argexp,
                     pretty funt,
                     pretty tp1',
                     pretty tp2'']
  return (tp1', tp2'')
  where sizeSubst (Prim (Signed Int32)) e = dimFromArg e
        sizeSubst _ _ = return AnyDim

checkApply loc tfun@TypeVar{} arg = do
  tv <- newTypeVar loc "b"
  unify loc (toStruct tfun) $ Arrow mempty Nothing (toStruct (argType arg)) tv
  constraints <- getConstraints
  checkApply loc (applySubst (`lookupSubst` constraints) tfun) arg

checkApply loc ftype arg =
  typeError loc $
  "Attempt to apply an expression of type " ++ pretty ftype ++
  " to an argument of type " ++ pretty (argType arg) ++ "."

isInt32 :: Exp -> Maybe Int32
isInt32 (Literal (SignedValue (Int32Value k')) _) = Just $ fromIntegral k'
isInt32 (IntLit k' _ _) = Just $ fromInteger k'
isInt32 _ = Nothing

dimFromArg :: Exp -> TermTypeM (DimDecl VName)
dimFromArg (Var v _ _) = return $ NamedDim v
dimFromArg (Parens e _) = dimFromArg e
dimFromArg (QualParens _ e _) = dimFromArg e
dimFromArg e
  | Just k <- isInt32 e = return $ ConstDim $ fromIntegral k
  | otherwise = do
      let e' = bareExp e
      prev <- gets $ M.lookup e' . stateDimTable
      case prev of
        Nothing -> do d <- newDimVar (srclocOf e) Rigid "argdim"
                      modify $ \s -> s { stateDimTable = M.insert e' d $
                                                         stateDimTable s }
                      return $ NamedDim $ qualName d
        Just d -> return $ NamedDim $ qualName d

instantiateEmptyArrayDims :: MonadUnify f =>
                             SrcLoc -> Rigidity -> TypeBase (DimDecl VName) als
                          -> f (TypeBase (DimDecl VName) als, [VName])
instantiateEmptyArrayDims loc r = runWriterT . instantiate
  where instantiate t@Array{} = bitraverse onDim pure t
        instantiate (Record fs) = Record <$> traverse instantiate fs
        instantiate t = return t

        onDim AnyDim = do v <- lift $ newDimVar loc r "impl_dim"
                          tell [v]
                          return $ NamedDim $ qualName v
        onDim d = pure d

-- | @returnType ret_type arg_diet arg_type@ gives result of applying
-- an argument the given types to a function with the given return
-- type, consuming the argument with the given diet.
returnType :: PatternType
           -> Diet
           -> PatternType
           -> PatternType
returnType (Array _ Unique et shape) _ _ =
  Array mempty Unique et shape
returnType (Array als Nonunique et shape) d arg =
  Array (als<>arg_als) Unique et shape -- Intentional!
  where arg_als = aliases $ maskAliases arg d
returnType (Record fs) d arg =
  Record $ fmap (\et -> returnType et d arg) fs
returnType (Prim t) _ _ = Prim t
returnType (TypeVar _ Unique t targs) _ _ =
  TypeVar mempty Unique t targs
returnType (TypeVar als Nonunique t targs) d arg =
  TypeVar (als<>arg_als) Unique t targs -- Intentional!
  where arg_als = aliases $ maskAliases arg d
returnType (Arrow _ v t1 t2) d arg =
  Arrow als v (t1 `setAliases` mempty) (t2 `setAliases` als)
  where als = aliases $ maskAliases arg d
returnType (Enum cs) _ _ = Enum cs

-- | @t `maskAliases` d@ removes aliases (sets them to 'mempty') from
-- the parts of @t@ that are denoted as 'Consumed' by the 'Diet' @d@.
maskAliases :: Monoid as =>
               TypeBase shape as
            -> Diet
            -> TypeBase shape as
maskAliases t Consume = t `setAliases` mempty
maskAliases t Observe = t
maskAliases (Record ets) (RecordDiet ds) =
  Record $ M.intersectionWith maskAliases ets ds
maskAliases t FuncDiet{} = t
maskAliases _ _ = error "Invalid arguments passed to maskAliases."

consumeArg :: SrcLoc -> PatternType -> Diet -> TermTypeM [Occurence]
consumeArg loc (Record ets) (RecordDiet ds) =
  concat . M.elems <$> traverse (uncurry $ consumeArg loc) (M.intersectionWith (,) ets ds)
consumeArg loc (Array _ Nonunique _ _) Consume =
  typeError loc "Consuming parameter passed non-unique argument."
consumeArg loc (Arrow _ _ t1 _) (FuncDiet d _)
  | not $ contravariantArg t1 d =
      typeError loc "Non-consuming higher-order parameter passed consuming argument."
  where contravariantArg (Array _ Unique _ _) Observe =
          False
        contravariantArg (TypeVar _ Unique _ _) Observe =
          False
        contravariantArg (Record ets) (RecordDiet ds) =
          and (M.intersectionWith contravariantArg ets ds)
        contravariantArg (Arrow _ _ tp tr) (FuncDiet dp dr) =
          contravariantArg tp dp && contravariantArg tr dr
        contravariantArg _ _ =
          True
consumeArg loc (Arrow _ _ _ t2) (FuncDiet _ pd) =
  consumeArg loc t2 pd
consumeArg loc at Consume = return [consumption (aliases at) loc]
consumeArg loc at _       = return [observation (aliases at) loc]

checkOneExp :: UncheckedExp -> TypeM ([TypeParam], Exp)
checkOneExp e = fmap fst . runTermTypeM $ do
  e' <- checkExp e
  let t = toStruct $ typeOf e'
  tparams <- letGeneralise [] t mempty
  fixOverloadedTypes
  e'' <- updateExpTypes mempty e'
  return (tparams, e'')

-- | Type-check a top-level (or module-level) function definition.
-- Despite the name, this is also used for checking constant
-- definitions, by treating them as 0-ary functions.
checkFunDef :: (Name, Maybe UncheckedTypeExp,
                [UncheckedTypeParam], [UncheckedPattern],
                UncheckedExp, SrcLoc)
            -> TypeM (VName, [TypeParam], [Pattern], Maybe (TypeExp VName), StructType, Exp)
checkFunDef f = fmap fst $ runTermTypeM $ do
  (fname, tparams, params, maybe_retdecl, rettype, body) <- checkFunDef' f

  -- Since this is a top-level function, we also resolve overloaded
  -- types, using either defaults or complaining about ambiguities.
  fixOverloadedTypes

  -- Then replace all inferred types in the body and parameters.
  body' <- updateExpTypes tparams body
  params' <- updateExpTypes tparams params
  maybe_retdecl' <- traverse (updateExpTypes tparams) maybe_retdecl
  rettype' <- normaliseType rettype

  -- Check if pattern matches are exhaustive and yield
  -- errors if not.
  checkUnmatched body'

  return (fname, tparams, params', maybe_retdecl', rettype', body')

-- | This is "fixing" as in "setting them", not "correcting them".  We
-- only make very conservative fixing.
fixOverloadedTypes :: TermTypeM ()
fixOverloadedTypes = getConstraints >>= mapM_ fixOverloaded . M.toList
  where fixOverloaded (v, Overloaded ots loc)
          | Signed Int32 `elem` ots = do
              unify loc (TypeVar () Nonunique (typeName v) []) $ Prim $ Signed Int32
              warn loc "Defaulting ambiguous type to `i32`."
          | FloatType Float64 `elem` ots = do
              unify loc (TypeVar () Nonunique (typeName v) []) $ Prim $ FloatType Float64
              warn loc "Defaulting ambiguous type to `f64`."
          | otherwise =
              typeError loc $
              unlines ["Type is ambiguous (could be one of " ++ intercalate ", " (map pretty ots) ++ ").",
                       "Add a type annotation to disambiguate the type."]

        fixOverloaded (_, NoConstraint _ loc) =
          typeError loc $ unlines ["Type of expression is ambiguous.",
                                    "Add a type annotation to disambiguate the type."]

        fixOverloaded (_, Equality loc) =
          typeError loc $ unlines ["Type is ambiguous (must be equality type).",
                                   "Add a type annotation to disambiguate the type."]

        fixOverloaded (_, HasFields fs loc) =
          typeError loc $ unlines ["Type is ambiguous (must be record with fields {" ++ fs' ++ "}).",
                                   "Add a type annotation to disambiguate the type."]
          where fs' = intercalate ", " $ map field $ M.toList fs
                field (l, t) = pretty l ++ ": " ++ pretty t

        fixOverloaded (_, HasConstrs cs loc) =
          typeError loc $ unlines [ "Type is ambiguous (must be an enum with constructors: " ++ cs' ++ ")."
                                    ,"Add a type annotation to disambiguate the type."]
          where cs' = intercalate " | " $ map (\c -> '#' : pretty c) cs

        fixOverloaded _ = return ()

checkFunDef' :: (Name, Maybe UncheckedTypeExp,
                 [UncheckedTypeParam], [UncheckedPattern],
                 UncheckedExp, SrcLoc)
             -> TermTypeM (VName, [TypeParam], [Pattern], Maybe (TypeExp VName), StructType, Exp)
checkFunDef' (fname, maybe_retdecl, tparams, params, body, loc) = noUnique $ do
  when (nameToString fname == "&&") $
    typeError loc "The && operator may not be redefined."
  when (nameToString fname == "||") $
    typeError loc "The || operator may not be redefined."

  then_substs <- getConstraints

  bindingParams tparams params $ \tparams' params' -> do
    maybe_retdecl' <- traverse checkTypeExp maybe_retdecl

    body' <- checkFunBody body ((\(_,t,_)->t) <$> maybe_retdecl') (maybe loc srclocOf maybe_retdecl)

    params'' <- updateExpTypes tparams' params'
    body_t <- expType body'

    (maybe_retdecl'', rettype) <- case maybe_retdecl' of
      Just (retdecl', retdecl_type, _) -> do
        let rettype_structural = toStructural retdecl_type
        checkReturnAlias rettype_structural params'' body_t

        when (null params) $ nothingMustBeUnique loc rettype_structural

        warnOnDubiousShapeAnnotations loc params'' retdecl_type

        return (Just retdecl', retdecl_type)
      Nothing
        | null params ->
            return (Nothing, toStruct $ body_t `setUniqueness` Nonunique)
        | otherwise ->
            return (Nothing, inferReturnUniqueness params'' body_t)

    let fun_t = foldFunType (map patternStructType params'') rettype
    tparams'' <- letGeneralise tparams' fun_t then_substs

    bindSpaced [(Term, fname)] $ do
      fname' <- checkName Term fname loc
      checkGlobalAliases params'' body_t loc

      variables <- S.fromList . M.keys <$> getConstraints
      let (params''', rettype') = cleanSignature variables tparams'' params'' rettype
          msg = unlines [prettyName fname',
                         unwords [pretty params''', pretty rettype']]

      return (fname', tparams'', params''', maybe_retdecl'', rettype', body')

  where -- | Check that unique return values do not alias a
        -- non-consumed parameter.
        checkReturnAlias rettp params' =
          foldM_ (checkReturnAlias' params') S.empty . returnAliasing rettp
        checkReturnAlias' params' seen (Unique, names)
          | any (`S.member` S.map snd seen) $ S.toList names =
              uniqueReturnAliased fname loc
          | otherwise = do
              notAliasingParam params' names
              return $ seen `S.union` tag Unique names
        checkReturnAlias' _ seen (Nonunique, names)
          | any (`S.member` seen) $ S.toList $ tag Unique names =
            uniqueReturnAliased fname loc
          | otherwise = return $ seen `S.union` tag Nonunique names

        notAliasingParam params' names =
          forM_ params' $ \p ->
          let consumedNonunique p' =
                not (unique $ unInfo $ identType p') && (identName p' `S.member` names)
          in case find consumedNonunique $ S.toList $ patternIdents p of
               Just p' ->
                 returnAliased fname (baseName $ identName p') loc
               Nothing ->
                 return ()

        tag u = S.map $ \name -> (u, name)

        returnAliasing (Record ets1) (Record ets2) =
          concat $ M.elems $ M.intersectionWith returnAliasing ets1 ets2
        returnAliasing expected got =
          [(uniqueness expected, S.map aliasVar $ aliases got)]

warnOnDubiousShapeAnnotations :: SrcLoc -> [Pattern] -> StructType -> TermTypeM ()
warnOnDubiousShapeAnnotations loc params rettype =
  onDubiousNames $ S.filter patternNameButNotParamName $
  mconcat $ map typeDimNames $
  rettype : map patternStructType params
  where param_names = S.fromList $ mapMaybe (fst . patternParam) params
        all_pattern_names = S.map identName $ mconcat $ map patternIdents params
        patternNameButNotParamName v = v `S.member` all_pattern_names && not (v `S.member` param_names)
        onDubiousNames dubious
          | S.null dubious = return ()
          | otherwise = warn loc $ unlines
                        [ "Size annotations in parameter and/or return type refers to the following names,"
                        , "which will not be visible to the caller, because they are nested in tuples or records:"
                        , "  " ++ intercalate ", " (map (quote . prettyName) $ S.toList dubious)
                        , "To eliminate this warning, make these names parameters on their own."]

-- | Remove all size annotations in the parameter- and return types
-- that refer to names that will not be visible in the outside
-- signature.  The constraints will still be in effect inside the
-- function definition, but invisible to the caller.
cleanSignature :: S.Set VName -> [TypeParam] -> [Pattern] -> StructType -> ([Pattern], StructType)
cleanSignature variables tparams params rettype =
  let all_pattern_names = S.map identName $ mconcat $ map patternIdents params
      param_names = map typeParamName tparams ++
                    mapMaybe (fst . patternParam) params
      anyDimIfNonparam v
        | v `elem` param_names = mempty
        | otherwise = M.singleton v $ SizeSubst AnyDim
      substs :: M.Map VName (Subst StructType)
      substs = mconcat $ map anyDimIfNonparam $ S.toList $
               variables <> all_pattern_names
  in (map (applySubst (`M.lookup` substs)) params,
      applySubst (`M.lookup` substs) rettype)

checkGlobalAliases :: [Pattern] -> PatternType -> SrcLoc -> TermTypeM ()
checkGlobalAliases params body_t loc = do
  vtable <- asks scopeVtable
  let isLocal v = case v `M.lookup` vtable of
                    Just (BoundV Local _ _) -> True
                    _ -> False
  let als = filter (not . isLocal) $ S.toList $
            boundArrayAliases body_t `S.difference`
            S.map identName (mconcat (map patternIdents params))
  case als of
    v:_ | not $ null params ->
      typeError loc $
      unlines [ "Function result aliases the free variable " <>
                quote (prettyName v) <> "."
              , "Use " ++ quote "copy" ++ " to break the aliasing."]
    _ ->
      return ()


inferReturnUniqueness :: [Pattern] -> PatternType -> StructType
inferReturnUniqueness params t =
  let forbidden = aliasesMultipleTimes t
      uniques = uniqueParamNames params
      delve (Record fs) =
        Record $ M.map delve fs
      delve t'
        | all (`S.member` uniques) (boundArrayAliases t'),
          not $ any ((`S.member` forbidden) . aliasVar) (aliases t') =
            toStruct t'
        | otherwise =
            toStruct $ t' `setUniqueness` Nonunique
  in delve t

-- An alias inhibits uniqueness if it is used in disjoint values.
aliasesMultipleTimes :: PatternType -> Names
aliasesMultipleTimes = S.fromList . map fst . filter ((>1) . snd) . M.toList . delve
  where delve (Record fs) =
          foldl' (M.unionWith (+)) mempty $ map delve $ M.elems fs
        delve t =
          M.fromList $ zip (map aliasVar $ S.toList (aliases t)) $ repeat (1::Int)

uniqueParamNames :: [Pattern] -> Names
uniqueParamNames =
  S.fromList . map identName
  . filter (unique . unInfo . identType)
  . S.toList . mconcat . map patternIdents

boundArrayAliases :: PatternType -> S.Set VName
boundArrayAliases (Array als _ _ _) = boundAliases als
boundArrayAliases Prim{} = mempty
boundArrayAliases Enum{} = mempty
boundArrayAliases (Record fs) = foldMap boundArrayAliases fs
boundArrayAliases (TypeVar als _ _ _) = boundAliases als
boundArrayAliases Arrow{} = mempty

-- | The set of in-scope variables that are being aliased.
boundAliases :: Aliasing -> S.Set VName
boundAliases = S.map aliasVar . S.filter bound
  where bound AliasBound{} = True
        bound AliasFree{} = False

nothingMustBeUnique :: SrcLoc -> TypeBase () () -> TermTypeM ()
nothingMustBeUnique loc = check
  where check (Array _ Unique _ _) = bad
        check (TypeVar _ Unique _ _) = bad
        check (Record fs) = mapM_ check fs
        check _ = return ()
        bad = typeError loc "A top-level constant cannot have a unique type."

letGeneralise :: [TypeParam]
              -> StructType
              -> Constraints
              -> TermTypeM [TypeParam]
letGeneralise tparams t then_substs = do
  now_substs <- getConstraints
  -- Candidates for let-generalisation are those type variables that
  --
  -- (1) were not known before we checked this function, and
  --
  -- (2) are not used in the (new) definition of any type variables
  -- known before we checked this function.
  --
  -- (3) are not referenced from an overloaded type (for example,
  -- are the element types of an incompletely resolved record type).
  -- This is a bit more restrictive than I'd like, and SML for
  -- example does not have this restriction.
  let then_type_variables = S.fromList $ M.keys then_substs
      then_type_constraints = constraintTypeVars $
                              M.filterWithKey (\k _ -> k `S.member` then_type_variables) now_substs
      keep_type_variables = then_type_variables <>
                            then_type_constraints <>
                            overloadedTypeVars now_substs

  let new_substs = M.filterWithKey (\k _ -> not (k `S.member` keep_type_variables)) now_substs
  tparams' <- closeOverTypes new_substs tparams t

  -- We keep those type variables that were not closed over by
  -- let-generalisation.
  modifyConstraints $ M.filterWithKey $ \k _ -> k `notElem` map typeParamName tparams'

  return tparams'

checkFunBody :: ExpBase NoInfo Name
             -> Maybe StructType
             -> SrcLoc
             -> TermTypeM Exp
checkFunBody body maybe_rettype loc = do
  body' <- checkExp body

  -- Unify body return type with return annotation, if one exists.
  case maybe_rettype of
    Just rettype -> do
      (rettype_withdims, _) <- instantiateEmptyArrayDims loc Nonrigid rettype

      body_t <- expType body'
      let msg = unlines ["return-unifying",
                         pretty rettype_withdims,
                         pretty body_t]
      unify (srclocOf body) rettype_withdims $ toStruct body_t

      -- We also have to make sure that uniqueness matches.  This is done
      -- explicitly, because uniqueness is ignored by unification.
      rettype' <- normaliseType rettype
      body_t' <- normaliseType rettype -- Substs may have changed.
      unless (body_t' `subtypeOf` rettype') $
        typeError (srclocOf body) $ "Body type " ++ quote (pretty body_t') ++
        " is not a subtype of annotated type " ++
        quote (pretty rettype') ++ "."

    Nothing -> return ()

  return body'

-- | Find at all type variables in the given type that are covered by
-- the constraints, and produce type parameters that close over them.
-- Produce an error if the given list of type parameters is non-empty,
-- yet does not cover all type variables in the type.
closeOverTypes :: Constraints -> [TypeParam] -> StructType -> TermTypeM [TypeParam]
closeOverTypes substs tparams t =
  case tparams of
    [] -> fmap catMaybes $ mapM closeOver $ M.toList substs'
    _ -> do mapM_ checkClosedOver $ M.toList substs'
            return tparams
  where substs' = M.filterWithKey (\k _ -> k `S.member` visible) substs
        visible = typeVars t <> typeDimNames t

        checkClosedOver (k, v)
          | not (mustBeClosedOver v) ||
            k `elem` map typeParamName tparams =
              return ()
          | otherwise =
              typeError (srclocOf v) $
              unlines ["Type variable " ++ quote (prettyName k) ++
                        " not closed over by type parameters " ++
                        intercalate ", " (map pretty tparams) ++ ".",
                        "This is usually because a parameter needs a type annotation."]

        mustBeClosedOver NoConstraint{} = True
        mustBeClosedOver _ = False

        closeOver (k, NoConstraint (Just Unlifted) loc) = return $ Just $ TypeParamType Unlifted k loc
        closeOver (k, NoConstraint _ loc) = return $ Just $ TypeParamType Lifted k loc
        closeOver (k, Size Nothing loc) = return $ Just $ TypeParamDim k loc
        closeOver (_, _) = return Nothing

--- Consumption

occur :: Occurences -> TermTypeM ()
occur = tell

-- | Proclaim that we have made read-only use of the given variable.
observe :: Ident -> TermTypeM ()
observe (Ident nm (Info t) loc) =
  let als = AliasBound nm `S.insert` aliases t
  in occur [observation als loc]

-- | Proclaim that we have written to the given variable.
consume :: SrcLoc -> Aliasing -> TermTypeM ()
consume loc als = do
  vtable <- asks scopeVtable
  let consumable v = case M.lookup v vtable of
                       Just (BoundV Local _ t)
                         | arrayRank t > 0 -> unique t
                         | otherwise -> True
                       _ -> False
  case filter (not . consumable) $ map aliasVar $ S.toList als of
    v:_ -> typeError loc $ "Attempt to consume variable " ++ quote (prettyName v)
           ++ ", which is not allowed."
    [] -> occur [consumption als loc]

-- | Proclaim that we have written to the given variable, and mark
-- accesses to it and all of its aliases as invalid inside the given
-- computation.
consuming :: Ident -> TermTypeM a -> TermTypeM a
consuming (Ident name (Info t) loc) m = do
  consume loc $ AliasBound name `S.insert` aliases t
  local consume' m
  where consume' scope =
          scope { scopeVtable = M.insert name (WasConsumed loc) $ scopeVtable scope }

collectOccurences :: TermTypeM a -> TermTypeM (a, Occurences)
collectOccurences m = pass $ do
  (x, dataflow) <- listen m
  return ((x, dataflow), const mempty)

tapOccurences :: TermTypeM a -> TermTypeM (a, Occurences)
tapOccurences = listen

removeSeminullOccurences :: TermTypeM a -> TermTypeM a
removeSeminullOccurences = censor $ filter $ not . seminullOccurence

checkIfUsed :: Occurences -> Ident -> TermTypeM ()
checkIfUsed occs v
  | not $ identName v `S.member` allOccuring occs,
    not $ "_" `isPrefixOf` prettyName (identName v) =
      warn (srclocOf v) $ "Unused variable " ++ quote (pretty $ baseName $ identName v) ++ "."
  | otherwise =
      return ()

alternative :: TermTypeM a -> TermTypeM b -> TermTypeM (a,b)
alternative m1 m2 = pass $ do
  (x, occurs1) <- listen m1
  (y, occurs2) <- listen m2
  checkOccurences occurs1
  checkOccurences occurs2
  let usage = occurs1 `altOccurences` occurs2
  return ((x, y), const usage)

-- | Make all bindings nonunique.
noUnique :: TermTypeM a -> TermTypeM a
noUnique = local (\scope -> scope { scopeVtable = M.map set $ scopeVtable scope})
  where set (BoundV l tparams t)    = BoundV l tparams $ t `setUniqueness` Nonunique
        set (OverloadedF ts pts rt) = OverloadedF ts pts rt
        set EqualityF               = EqualityF
        set OpaqueF                 = OpaqueF
        set (WasConsumed loc)       = WasConsumed loc

onlySelfAliasing :: TermTypeM a -> TermTypeM a
onlySelfAliasing = local (\scope -> scope { scopeVtable = M.mapWithKey set $ scopeVtable scope})
  where set k (BoundV l tparams t)    = BoundV l tparams $
                                        t `addAliases` S.intersection (S.singleton (AliasBound k))
        set _ (OverloadedF ts pts rt) = OverloadedF ts pts rt
        set _ EqualityF               = EqualityF
        set _ OpaqueF                 = OpaqueF
        set _ (WasConsumed loc)       = WasConsumed loc

arrayOfM :: (Pretty (ShapeDecl dim), Monoid as) =>
            SrcLoc
         -> TypeBase dim as -> ShapeDecl dim -> Uniqueness
         -> TermTypeM (TypeBase dim as)
arrayOfM loc t shape u = do
  zeroOrderType loc "used in array" t
  maybe nope return $ arrayOf t shape u
  where nope = typeError loc $
               "Cannot form an array with elements of type " ++ pretty t

-- | Perform substitutions of instantiated variables on the type
-- annotations (including the instance lists) of an expression, or
-- something else.  We also remove all non-bound size parameters
-- (i.e. the ones that were instantiated for unknown array sizes
-- during type inference).
updateExpTypes :: ASTMappable e => [TypeParam] -> e -> TermTypeM e
updateExpTypes orig_tparams x = do
  constraints <- getConstraints
  let onType :: Substitutable (TypeBase (DimDecl VName) als) =>
                TypeBase (DimDecl VName) als
             -> Reader (S.Set VName) (TypeBase (DimDecl VName) als)
      onType t = do
        known_dims <- ask
        let anyDimIfUnknown v
              | v `S.member` known_dims = mempty
              | otherwise = M.singleton v $ SizeSubst AnyDim
            t' = applySubst (`lookupSubst` constraints) t
            dim_substs = mconcat $ map anyDimIfUnknown $ S.toList $ typeDimNames t'
        return $ applySubst (`M.lookup` dim_substs) t'
      tv = ASTMapper { mapOnExp         = onExp tv
                     , mapOnName        = pure
                     , mapOnQualName    = pure
                     , mapOnStructType  = onType
                     , mapOnPatternType = onType
                     }
  return $ runReader (astMap tv x) (binds orig_tparams)
  where binds = S.fromList . map typeParamName

        -- We special-case all expressions that bind size parameters.
        -- I hope I did not miss any.
        onExp tv e@(Lambda tparams _ _ _ _ _) =
          local (<> binds tparams) $ astMap tv e
        onExp tv e@(LetFun _ (tparams, _, _, _, _) _ _) =
          local (<> binds tparams) $ astMap tv e
        onExp tv e =
          astMap tv e
