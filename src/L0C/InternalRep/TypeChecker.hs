{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
-- | The type checker checks whether the program is type-consistent.
-- Whether type annotations are already present is irrelevant, but if
-- they are, the type checker will signal an error if they are wrong.
-- The program does not need to have any particular properties for the
-- type checker to function; in particular it does not need unique
-- names.
module L0C.InternalRep.TypeChecker
  ( checkProg
  , checkProgNoUniqueness
  , checkClosedExp
  , checkOpenExp
  , TypeError)
  where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.RWS
import Data.List
import Data.Loc

import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS

import L0C.InternalRep
import qualified L0C.FreshNames as FreshNames
import L0C.InternalRep.MonadFreshNames
import L0C.TypeError

type TypeError = GenTypeError VName Exp (Several Type) (Several Ident)

-- | A tuple of a return type and a list of argument types.
type FunBinding = ([DeclType], [DeclType])

data Binding = Bound Type
             | WasConsumed SrcLoc

data Usage = Consumed SrcLoc
           | Observed SrcLoc
             deriving (Eq, Ord, Show)

data Occurence = Occurence { observed :: Names
                           , consumed :: Names
                           , location :: SrcLoc
                           }
             deriving (Eq, Show)

instance Located Occurence where
  locOf = locOf . location

observation :: Names -> SrcLoc -> Occurence
observation = flip Occurence HS.empty

consumption :: Names -> SrcLoc -> Occurence
consumption = Occurence HS.empty

nullOccurence :: Occurence -> Bool
nullOccurence occ = HS.null (observed occ) && HS.null (consumed occ)

type Occurences = [Occurence]

type UsageMap = HM.HashMap VName [Usage]

usageMap :: Occurences -> UsageMap
usageMap = foldl comb HM.empty
  where comb m (Occurence obs cons loc) =
          let m' = HS.foldl' (ins $ Observed loc) m obs
          in HS.foldl' (ins $ Consumed loc) m' cons
        ins v m k = HM.insertWith (++) k [v] m

combineOccurences :: VName -> Usage -> Usage -> Either TypeError Usage
combineOccurences _ (Observed loc) (Observed _) = Right $ Observed loc
combineOccurences name (Consumed wloc) (Observed rloc) =
  Left $ UseAfterConsume name rloc wloc
combineOccurences name (Observed rloc) (Consumed wloc) =
  Left $ UseAfterConsume name rloc wloc
combineOccurences name (Consumed loc1) (Consumed loc2) =
  Left $ UseAfterConsume name (max loc1 loc2) (min loc1 loc2)

checkOccurences :: Occurences -> Either TypeError ()
checkOccurences = void . HM.traverseWithKey comb . usageMap
  where comb _    []     = Right ()
        comb name (u:us) = foldM_ (combineOccurences name) u us

allConsumed :: Occurences -> Names
allConsumed = HS.unions . map consumed

seqOccurences :: Occurences -> Occurences -> Occurences
seqOccurences occurs1 occurs2 =
  filter (not . nullOccurence) $ map filt occurs1 ++ occurs2
  where filt occ =
          occ { observed = observed occ `HS.difference` postcons }
        postcons = allConsumed occurs2

altOccurences :: Occurences -> Occurences -> Occurences
altOccurences occurs1 occurs2 =
  filter (not . nullOccurence) $ map filt occurs1 ++ occurs2
  where filt occ =
          occ { consumed = consumed occ `HS.difference` postcons
              , observed = observed occ `HS.difference` postcons }
        postcons = allConsumed occurs2


-- | The 'VarUsage' data structure is used to keep track of which
-- variables have been referenced inside an expression, as well as
-- which variables the resulting expression may possibly alias.
data Dataflow = Dataflow {
    usageOccurences :: Occurences
  } deriving (Show)

instance Monoid Dataflow where
  mempty = Dataflow mempty
  Dataflow o1 `mappend` Dataflow o2 =
    Dataflow (o1 ++ o2)

-- | A pair of a variable table and a function table.  Type checking
-- happens with access to this environment.  The function table is
-- only initialised at the very beginning, but the variable table will
-- be extended during type-checking when let-expressions are
-- encountered.
data TypeEnv = TypeEnv { envVtable :: HM.HashMap VName Binding
                       , envFtable :: HM.HashMap Name FunBinding
                       , envCheckOccurences :: Bool
                       }

-- | The type checker runs in this monad.  The 'Either' monad is used
-- for error handling.
newtype TypeM a = TypeM (RWST
                         TypeEnv            -- Reader
                         Dataflow           -- Writer
                         (NameSource VName) -- State
                         (Either TypeError) -- Inner monad
                         a)
  deriving (Monad, Functor, Applicative,
            MonadReader TypeEnv,
            MonadWriter Dataflow,
            MonadState VNameSource)

runTypeM :: TypeEnv -> NameSource VName -> TypeM a
         -> Either TypeError a
runTypeM env src (TypeM m) = fst <$> evalRWST m env src

bad :: TypeError -> TypeM a
bad = TypeM . lift . Left

instance MonadFreshNames VName TypeM where
  getNameSource = get
  putNameSource = put

newFname :: String -> TypeM Name
newFname s = do s' <- state (`FreshNames.newID` varName s Nothing)
                return $ nameFromString $ textual $ baseName s'

liftEither :: Either TypeError a -> TypeM a
liftEither = either bad return

occur :: Occurences -> TypeM ()
occur occurs = tell Dataflow { usageOccurences = occurs }

-- | Proclaim that we have made read-only use of the given variable.
-- No-op unless the variable is array-typed.
observe :: Ident -> TypeM ()
observe (Ident nm t loc)
  | basicType t = return ()
  | otherwise   = let als = nm `HS.insert` aliases t
                  in occur [observation als loc]

-- | Proclaim that we have written to the given variable.
consume :: SrcLoc -> Names -> TypeM ()
consume loc als = occur [consumption als loc]

-- | Proclaim that we have written to the given variable, and mark
-- accesses to it and all of its aliases as invalid inside the given
-- computation.
consuming :: Ident -> TypeM a -> TypeM a
consuming (Ident name t loc) m = do
  consume loc $ aliases t
  local consume' m
  where consume' env =
          env { envVtable = HM.insert name (WasConsumed loc) $ envVtable env }

collectDataflow :: TypeM a -> TypeM (a, Dataflow)
collectDataflow m = pass $ do
  (x, dataflow) <- listen m
  return ((x, dataflow), const mempty)

patDiet :: [Ident] -> Occurences -> [Diet]
patDiet pat occs = map patDiet' pat
  where cons =  allConsumed occs
        patDiet' k
          | identName k `HS.member` cons = Consume
          | otherwise                    = Observe

maybeCheckOccurences :: Occurences -> TypeM ()
maybeCheckOccurences us = do
  check <- asks envCheckOccurences
  when check $ liftEither $ checkOccurences us

alternative :: TypeM a -> TypeM b -> TypeM (a,b)
alternative m1 m2 = pass $ do
  (x, Dataflow occurs1) <- listen m1
  (y, Dataflow occurs2) <- listen m2
  maybeCheckOccurences occurs1
  maybeCheckOccurences occurs2
  let usage = Dataflow $ occurs1 `altOccurences` occurs2
  return ((x, y), const usage)

-- | Remove all variable bindings from the vtable inside the given
-- computation.
unbinding :: TypeM a -> TypeM a
unbinding = local (\env -> env { envVtable = HM.empty})

-- | Make all bindings nonunique.
noUnique :: TypeM a -> TypeM a
noUnique = local (\env -> env { envVtable = HM.map f $ envVtable env})
  where f (Bound t)         = Bound $ t `setUniqueness` Nonunique
        f (WasConsumed loc) = WasConsumed loc

binding :: [Ident] -> TypeM a -> TypeM a
binding bnds = check . local (`bindVars` bnds)
  where bindVars :: TypeEnv -> [Ident] -> TypeEnv
        bindVars = foldl bindVar

        bindVar :: TypeEnv -> Ident -> TypeEnv
        bindVar env (Ident name tp _) =
          let inedges = HS.toList $ aliases tp
              update (Bound tp') =
                Bound $ tp' `changeAliases` HS.insert name
              update b = b
          in env { envVtable = HM.insert name (Bound tp) $
                               adjustSeveral update inedges $
                               envVtable env }

        adjustSeveral f = flip $ foldl $ flip $ HM.adjust f

        -- Check whether the bound variables have been used correctly
        -- within their scope.
        check m = do
          (a, usages) <- collectOccurences m
          maybeCheckOccurences usages
          return a

        -- Collect and remove all occurences in @bnds@.  This relies
        -- on the fact that no variables shadow any other.
        collectOccurences m = pass $ do
          (x, usage) <- listen m
          let (relevant, rest) = split $ usageOccurences usage
          return ((x, relevant), const $ usage { usageOccurences = rest })
          where split = unzip .
                        map (\occ ->
                             let (obs1, obs2) = divide $ observed occ
                                 (con1, con2) = divide $ consumed occ
                             in (occ { observed = obs1, consumed = con1 },
                                 occ { observed = obs2, consumed = con2 }))
                names = HS.fromList $ map identName bnds
                divide s = (s `HS.intersection` names, s `HS.difference` names)

lookupVar :: VName -> SrcLoc -> TypeM Type
lookupVar name pos = do
  bnd <- asks $ HM.lookup name . envVtable
  case bnd of
    Nothing -> bad $ UnknownVariableError name pos
    Just (Bound t) -> return t
    Just (WasConsumed wloc) -> bad $ UseAfterConsume name pos wloc

-- | @t1 `unifyTypes` t2@ attempts to unify @t2@ and @t2@.  If
-- unification cannot happen, 'Nothing' is returned, otherwise a type
-- that combines the aliasing of @t1@ and @t2@ is returned.  The
-- uniqueness of the resulting type will be the least of the
-- uniqueness of @t1@ and @t2@.
unifyTypes :: Type -> Type -> Maybe Type
unifyTypes (Basic t1) (Basic t2) = Basic <$> t1 `unifyBasicTypes` t2
unifyTypes (Array t1 ds1 u1 als1) (Array t2 ds2 u2 als2)
  | length ds1 == length ds2 = do
  t <- t1 `unifyBasicTypes` t2
  Just $ Array t ds1 (u1 <> u2) (als1 <> als2)
unifyTypes _ _ = Nothing

-- | As 'unifyTypes', but for element types.
unifyBasicTypes :: BasicType -> BasicType -> Maybe BasicType
unifyBasicTypes t1 t2
  | t1 == t2  = Just t1
  | otherwise = Nothing

-- | Determine if two types are identical, ignoring uniqueness.
-- Causes a '(TypeError vn)' if they fail to match, and otherwise returns
-- one of them.
unifySubExpTypes :: SubExp -> SubExp -> TypeM Type
unifySubExpTypes e1 e2 =
  maybe (bad $ UnifyError (SubExp e1) (justOne t1) (SubExp e2) (justOne t2)) return $
  unifyTypes t1 t2
  where t1 = subExpType e1
        t2 = subExpType e2

-- | @checkAnnotation loc s t1 t2@ returns @t2@ if @t1@ contains no
-- type, and otherwise tries to unify them with 'unifyTypes'.  If
-- this fails, a 'BadAnnotation' is raised.
checkAnnotation :: SrcLoc -> String -> Type -> Type -> TypeM Type
checkAnnotation loc desc t1 t2 =
  case unifyTypes (t1 `setAliases` HS.empty) t2 of
    Nothing -> bad $ BadAnnotation loc desc (justOne t1) (justOne t2)
    Just t  -> return t

-- | @checkTupleAnnotation loc s t1s t2s@ tries to unify the types in
-- @t1s@ and @t2s@ with 'unifyTypes'.  If this fails, or @t1s@ and @t2s@ are not the same length, a
-- 'BadAnnotation' is raised.
checkTupleAnnotation :: SrcLoc -> String -> [Type] -> [Type] -> TypeM [Type]
checkTupleAnnotation loc desc t1s t2s
  | length t1s == length t2s,
    Just ts <- zipWithM unifyTypes t1s t2s = return ts
  | otherwise = bad $ BadAnnotation loc desc (Several t1s) (Several t2s)

-- | @require ts e@ causes a '(TypeError vn)' if @typeOf e@ does not unify
-- with one of the types in @ts@.  Otherwise, simply returns @e@.
-- This function is very useful in 'checkExp'.
require :: [Type] -> SubExp -> TypeM SubExp
require ts e
  | any (subExpType e `similarTo`) ts = return e
  | otherwise = bad $ UnexpectedType (SubExp e)
                      (justOne $ subExpType e)
                      (map justOne ts)

-- | Variant of 'require' working on identifiers.
requireI :: [Type] -> Ident -> TypeM Ident
requireI ts ident
  | any (identType ident `similarTo`) ts = return ident
  | otherwise = bad $ UnexpectedType (SubExp $ Var ident)
                      (justOne $ identType ident)
                      (map justOne ts)

rowTypeM :: SubExp -> TypeM Type
rowTypeM e = maybe wrong return $ peelArray 1 $ subExpType e
  where wrong = bad $ NotAnArray (srclocOf e) (SubExp e) $
                      justOne $ subExpType e

-- | Type check a program containing arbitrary type information,
-- yielding either a type error or a program with complete type
-- information.
checkProg :: Prog -> Either TypeError Prog
checkProg = checkProg' True

-- | As 'checkProg', but don't check whether uniqueness constraints
-- are being upheld.  The uniqueness of types must still be correct.
checkProgNoUniqueness :: Prog -> Either TypeError Prog
checkProgNoUniqueness = checkProg' False

checkProg' :: Bool -> Prog -> Either TypeError Prog
checkProg' checkoccurs prog = do
  ftable <- buildFtable
  let typeenv = TypeEnv { envVtable = HM.empty
                        , envFtable = ftable
                        , envCheckOccurences = checkoccurs
                        }

  liftM Prog $ runTypeM typeenv src $
        mapM checkFun $ progFunctions prog
  where
    src = newNameSourceForProg prog
    -- To build the ftable we loop through the list of function
    -- definitions.  In addition to the normal ftable information
    -- (name, return type, argument types), we also keep track of
    -- position information, in order to report both locations of
    -- duplicate function definitions.  The position information is
    -- removed at the end.
    buildFtable = HM.map rmLoc <$>
                  foldM expand (HM.map addLoc builtInFunctions)
                  (progFunctions prog)
    expand ftable (name,ret,args,_,pos)
      | Just (_,_,pos2) <- HM.lookup name ftable =
        Left $ DupDefinitionError name pos pos2
      | otherwise =
        let argtypes = map (toDecl . identType) args -- Throw away argument names.
        in Right $ HM.insert name (ret,argtypes,pos) ftable
    rmLoc (ret,args,_) = (ret,args)
    addLoc (t, ts) = (t, ts, noLoc)

builtInFunctions :: HM.HashMap Name FunBinding
builtInFunctions = HM.fromList $ map namify
                   [("toReal", ([Basic Real], [Basic Int]))
                   ,("trunc", ([Basic Int], [Basic Real]))
                   ,("sqrt", ([Basic Real], [Basic Real]))
                   ,("log", ([Basic Real], [Basic Real]))
                   ,("exp", ([Basic Real], [Basic Real]))
                   ,("op not", ([Basic Bool], [Basic Bool]))]
  where namify (k,v) = (nameFromString k, v)

checkFun :: FunDec -> TypeM FunDec
checkFun (fname, rettype, params, body, loc) = do
  params' <- checkParams
  (body', _) <-
    collectDataflow $ binding (map fromParam params') $ checkExp body

  checkReturnAlias $ typeOf body'

  if typeOf body' `subtypesOf` rettype then
    return (fname, rettype, params', body', loc)
  else bad $ ReturnTypeError loc fname
             (Several $ map fromDecl rettype)
             (Several $ typeOf body')

  where checkParams = reverse <$> foldM expand [] params

        expand params' ident@(Ident pname _ _)
          | Just _ <- find ((==identName ident) . identName) params' =
            bad $ DupParamError fname pname loc
          | otherwise =
            return $ ident : params'

        notAliasingParam names =
          forM_ params $ \p ->
            when (not (unique $ identType p) &&
                  identName p `HS.member` names) $
              bad $ ReturnAliased fname (identName p) loc

        -- | Check that unique return values do not alias a
        -- non-consumed parameter.
        checkReturnAlias =
          foldM_ checkReturnAlias' HS.empty . returnAliasing rettype

        checkReturnAlias' seen (Unique, names)
          | any (`HS.member` HS.map snd seen) $ HS.toList names =
            bad $ UniqueReturnAliased fname loc
          | otherwise = do
            notAliasingParam names
            return $ seen `HS.union` tag Unique names
        checkReturnAlias' seen (Nonunique, names)
          | any (`HS.member` seen) $ HS.toList $ tag Unique names =
            bad $ UniqueReturnAliased fname loc
          | otherwise = return $ seen `HS.union` tag Nonunique names

        tag u = HS.map $ \name -> (u, name)

        returnAliasing expected got =
          [ (uniqueness p, aliases t) |
            (p,t) <- zip expected got ]

-- | Type-check a single expression without any calls to non-builtin
-- functions.  Free variables are permitted, as long as they are
-- present in the passed-in vtable.
checkOpenExp :: HM.HashMap VName Type -> Exp ->
                Either TypeError Exp
checkOpenExp bnds e = runTypeM env (newNameSource frees) $ checkExp e
  where env = TypeEnv { envFtable = builtInFunctions
                      , envCheckOccurences = True
                      , envVtable = vtable
                      }

        frees = freeNamesInExp e

        vtable = HS.foldr tagBnd HM.empty frees
        tagBnd k m =
          case HM.lookup k bnds of
            Nothing -> m
            Just t  -> HM.insert k (Bound t) m

-- | Type-check a single expression without any free variables or
-- calls to non-builtin functions.
checkClosedExp :: Exp -> Either TypeError Exp
checkClosedExp e = runTypeM env src $ checkExp e
  where env = TypeEnv { envFtable = builtInFunctions
                      , envCheckOccurences = True
                      , envVtable = HM.empty
                      }
        src = newNameSource $ freeNamesInExp e

checkSubExp :: SubExp -> TypeM SubExp
checkSubExp (Constant v loc) =
  return $ Constant v loc
checkSubExp (Var ident) = do
  ident' <- checkIdent ident
  observe ident'
  return $ Var ident'

checkExp :: Exp -> TypeM Exp

checkExp (SubExp se) =
  SubExp <$> checkSubExp se

checkExp (TupLit es pos) = do
  es' <- mapM checkSubExp es
  return $ TupLit es' pos

checkExp (ArrayLit es t loc) = do
  es' <- mapM checkSubExp es
  -- Find the universal type of the array arguments.
  et <- case es' of
          [] -> bad $ TypeError loc "Empty array literal"
          e:es'' ->
            let check elemt eleme
                  | Just elemt' <- elemt `unifyTypes` subExpType eleme =
                    return elemt'
                  | otherwise =
                    bad $ TypeError loc $ undefined eleme ++ " is not of expected type " ++ undefined elemt ++ "."
            in foldM check (subExpType e) es''

  -- Unify that type with the one given for the array literal.
  t' <- checkAnnotation loc "array-element" t et

  return $ ArrayLit es' t' loc

checkExp (BinOp op e1 e2 t pos) = checkBinOp op e1 e2 t pos

checkExp (Not e pos) = do
  e' <- require [Basic Bool] =<< checkSubExp e
  return $ Not e' pos

checkExp (Negate e loc) = do
  e' <- require [Basic Int, Basic Real] =<< checkSubExp e
  return $ Negate e' loc

checkExp (If e1 e2 e3 t pos) = do
  e1' <- require [Basic Bool] =<< checkSubExp e1
  ((e2', e3'), dflow) <- collectDataflow $ checkExp e2 `alternative` checkExp e3
  tell dflow
  let removeConsumed = (`HS.difference` allConsumed (usageOccurences dflow))
  t' <- checkTupleAnnotation pos "branch result" t $
        map (`changeAliases` removeConsumed) $
        zipWith unifyUniqueness (typeOf e2') (typeOf e3')
  return $ If e1' e2' e3' t' pos

checkExp (Apply fname args t pos)
  | "trace" <- nameToString fname =
  case args of
    [(e, _)] -> do
      e'  <- checkSubExp e
      t'  <- checkTupleAnnotation pos "return" t [subExpType e']
      return $ Apply fname [(e', Observe)] t' pos
    _ -> bad $ TypeError pos "Trace function takes a single parameter"

checkExp (Apply fname args rettype loc) = do
  bnd <- asks $ HM.lookup fname . envFtable
  case bnd of
    Nothing -> bad $ UnknownFunctionError fname loc
    Just (ftype, paramtypes) -> do
      (args', argflows) <- unzip <$> mapM (checkArg . fst) args

      rettype' <- checkTupleAnnotation loc "return" rettype $
                  returnType ftype (map diet paramtypes) (map subExpType args')

      checkFuncall (Just fname) loc paramtypes (map toDecl rettype') argflows

      return $ Apply fname (zip args' $ map diet paramtypes) rettype' loc

checkExp (LetPat pat e body loc) = do
  (e', dataflow) <- collectDataflow $ checkExp e
  (scope, pat') <- checkBinding loc pat
                                (srclocOf e') (typeOf e')
                                dataflow
  scope $ do
    body' <- checkExp body
    return $ LetPat pat' e' body' loc

checkExp (LetWith cs (Ident dest destt destpos) src idxcs idxes ve body pos) = do
  cs' <- mapM (requireI [Basic Cert] <=< checkIdent) cs
  src' <- checkIdent src
  idxcs' <-
    case idxcs of
      Nothing       -> return Nothing
      Just idxcs' -> Just <$> mapM (requireI [Basic Cert] <=< checkIdent) idxcs'
  idxes' <- mapM (require [Basic Int] <=< checkSubExp) idxes
  destt' <- checkAnnotation pos "source" destt $ identType src' `setAliases` HS.empty
  let dest' = Ident dest destt' destpos

  unless (unique (identType src') || basicType (identType src')) $
    bad $ TypeError pos $ "Source '" ++ textual (baseName $ identName src) ++ "' is not unique"

  case peelArray (length idxes) (identType src') of
    Nothing -> bad $ IndexingError (identName src)
                     (arrayRank $ identType src') (length idxes) (srclocOf src)
    Just elemt ->
      sequentially (require [elemt] =<< checkSubExp ve) $ \ve' _ -> do
        when (identName src `HS.member` aliases (subExpType ve')) $
          bad $ BadLetWithValue pos
        (scope, _) <- checkBinding (srclocOf dest') [dest']
                                   (srclocOf dest') [destt']
                                   mempty
        body' <- consuming src' $ scope $ checkExp body
        return $ LetWith cs' dest' src' idxcs' idxes' ve' body' pos

checkExp (Index cs ident csidxes idxes pos) = do
  cs' <- mapM (requireI [Basic Cert] <=< checkIdent) cs
  csidxes' <-
    case csidxes of
      Nothing       -> return Nothing
      Just csidxes' -> Just <$> mapM (requireI [Basic Cert] <=< checkIdent) csidxes'
  ident' <- checkIdent ident
  observe ident'
  vt <- lookupVar (identName ident') pos
  when (arrayRank vt < length idxes) $
    bad $ IndexingError (identName ident)
          (arrayRank vt) (length idxes) pos
  idxes' <- mapM (require [Basic Int] <=< checkSubExp) idxes
  return $ Index cs' ident' csidxes' idxes' pos

checkExp (Iota e pos) = do
  e' <- require [Basic Int] =<< checkSubExp e
  return $ Iota e' pos

checkExp (Size cs i e pos) = do
  e' <- checkSubExp e
  cs' <- mapM (requireI [Basic Cert] <=< checkIdent) cs
  case subExpType e' of
    Array {}
      | i >= 0 && i < arrayRank (subExpType e') ->
        return $ Size cs' i e' pos
      | otherwise ->
        bad $ TypeError pos $ "Type " ++ undefined (subExpType e') ++ " has no dimension " ++ show i ++ "."
    _        -> bad $ TypeError pos "Argument to size must be array."

checkExp (Replicate countexp valexp pos) = do
  countexp' <- require [Basic Int] =<< checkSubExp countexp
  valexp' <- checkSubExp valexp
  return $ Replicate countexp' valexp' pos

checkExp (Reshape cs shapeexps arrexp pos) = do
  cs' <- mapM (requireI [Basic Cert] <=< checkIdent) cs
  shapeexps' <- mapM (require [Basic Int] <=< checkSubExp) shapeexps
  arrexp' <- checkSubExp arrexp
  return (Reshape cs' shapeexps' arrexp' pos)

checkExp (Transpose cs k n arrexp pos) = do
  cs' <- mapM (requireI [Basic Cert] <=< checkIdent) cs
  arrexp' <- checkSubExp arrexp
  when (arrayRank (subExpType arrexp') < reach + 1) $
    bad $ TypeError pos $ "Argument to transpose does not have " ++
          show (reach+1) ++ " dimensions."
  return $ Transpose cs' k n arrexp' pos
  where reach = max k $ n + k

checkExp (Split cs splitexp arrexp pos) = do
  cs' <- mapM (requireI [Basic Cert] <=< checkIdent) cs
  splitexp' <- require [Basic Int] =<< checkSubExp splitexp
  arrexp' <- checkSubExp arrexp
  _ <- rowTypeM arrexp' -- Just check that it's an array.
  return $ Split cs' splitexp' arrexp' pos

checkExp (Concat cs arr1exp arr2exp pos) = do
  cs' <- mapM (requireI [Basic Cert] <=< checkIdent) cs
  arr1exp' <- checkSubExp arr1exp
  arr2exp' <- require [subExpType arr1exp'] =<< checkSubExp arr2exp
  _ <- rowTypeM arr2exp' -- Just check that it's an array.
  return $ Concat cs' arr1exp' arr2exp' pos

checkExp (Copy e pos) = do
  e' <- checkSubExp e
  return $ Copy e' pos

checkExp (Assert e pos) = do
  e' <- require [Basic Bool] =<< checkSubExp e
  return $ Assert e' pos

checkExp (Conjoin es pos) = do
  es' <- mapM (require [Basic Cert] <=< checkSubExp) es
  return $ Conjoin es' pos

-- Checking of loops is done by synthesing the (almost) equivalent
-- function and type-checking a call to it.  The difficult part is
-- assigning uniqueness attributes to the parameters of the function -
-- we'll do this by inspecting the loop body, and look at which of the
-- variables in mergepat are actually consumed.  Also, any variables
-- that are free in the loop body must be passed along as (non-unique)
-- parameters to the function.
checkExp (DoLoop mergepat (Ident loopvar _ _)
          boundexp loopbody letbody loc) = do
  let (mergevs, es) = unzip mergepat
  -- First, check the bound and initial merge expression and throw
  -- away the dataflow.  The dataflow will be reconstructed later, but
  -- we need the result of this to synthesize the function.
  ((boundexp', es'), _) <-
    collectDataflow $ do boundexp' <- require [Basic Int] =<< checkSubExp boundexp
                         es'       <- mapM checkSubExp es
                         return (boundexp', es')
  let iparam = Ident loopvar (Basic Int) loc

  -- Check the loop body.  We tap the dataflow before leaving scope,
  -- so we'll be able to see occurences of variables bound by
  -- mergepat.
  (firstscope, mergevs') <-
    checkBinding loc mergevs loc (map subExpType es') mempty
  (loopbody', loopflow) <-
    firstscope $ collectDataflow $ binding [iparam] $ checkExp loopbody

  -- We can use the name generator in a slightly hacky way to generate
  -- a unique Name for the function.
  bound <- newIdent "loop_bound" (Basic Int) loc
  fname <- newFname "loop_fun"

  let -- | Change the uniqueness attribute of a type to reflect how it
      -- was used.
      param (Array et sz _ _) con = Array et sz u ()
        where u = case con of Consume     -> Unique
                              Observe     -> Nonunique
      param (Basic bt) _ = Basic bt

      -- We use the type of the merge expression, but with uniqueness
      -- attributes reflected to show how the parts of the merge
      -- pattern are used - if something was consumed, it has to be a
      -- unique parameter to the function.
      rettype = zipWith param (map subExpType es') $
                patDiet mergevs' $
                usageOccurences loopflow

  merge <- newIdents "merge_val" (map fromDecl rettype) loc

  let boundnames = HS.insert iparam $ HS.fromList mergevs'
      ununique ident =
        ident { identType = param (identType ident) Observe }
      -- Find the free variables of the loop body.
      free = map ununique $ HS.toList $
             freeInExp loopbody' `HS.difference` boundnames

      -- These are the parameters expected by the function: All of the
      -- free variables, followed by the index, followed by the upper
      -- bound (currently not used), followed by the merge value.
      params = free ++
               [iparam, toParam bound] ++ map toParam merge
      bindfun env = env { envFtable = HM.insert fname
                                      (rettype, map identType params) $
                                      envFtable env }

      -- The body of the function will be the loop body, but with all
      -- tails replaced with recursive calls.
      recurse e = do
        call <- newIdents "tail" (typeOf e) loc
        let bindArgs apply = LetPat call e apply loc
        return $ bindArgs $
                  Apply fname
                  ([(Var (fromParam k), diet (identType k)) | k <- free ] ++
                   [(Var iparam, Observe),
                    (Var bound, Observe)] ++
                   zip (map Var call) (map diet $ typeOf e))
                  (map fromDecl rettype) (srclocOf e)
  funbody' <- LetPat mergevs' (TupLit (map Var merge) loc) <$>
              mapTailsM recurse return loopbody' <*>
              pure (srclocOf loopbody')

  (funcall, callflow) <- collectDataflow $ local bindfun $ do
    -- Check that the function is internally consistent.
    _ <- unbinding $ checkFun (fname, rettype, params, funbody', loc)
    -- Check the actual function call - we start by computing the
    -- bound and initial merge value, in case they use something
    -- consumed in the call.  This reintroduces the dataflow for
    -- boundexp and mergeexp that we previously threw away.
    checkExp $ LetPat merge (TupLit es' loc)
               (Apply fname
                  ([(Var (fromParam k), diet (identType k)) | k <- free ] ++
                   [(Constant (BasicVal $ IntVal 0) loc, Observe),
                    (boundexp', Observe)] ++
                   zip (map Var merge) (map diet rettype))
                  (map fromDecl rettype) loc)
               loc

  -- Now we just need to bind the result of the function call to the
  -- original merge pattern...
  (secondscope, _) <- checkBinding loc mergevs loc (typeOf funcall) callflow

  -- And then check the let-body.
  secondscope $ do
    letbody' <- checkExp letbody
    return $ DoLoop (zip mergevs' es')
                    (Ident loopvar (Basic Int) loc) boundexp'
                    loopbody' letbody' loc

checkExp (Map ass fun arrexps pos) = do
  ass' <- mapM (requireI [Basic Cert] <=< checkIdent) ass
  (arrexps', arrargs) <- unzip <$> mapM checkSOACArrayArg arrexps
  fun'    <- checkLambda fun arrargs
  return $ Map ass' fun' arrexps' pos

checkExp (Reduce ass fun inputs pos) = do
  let (startexps, arrexps) = unzip inputs
  ass' <- mapM (requireI [Basic Cert] <=< checkIdent) ass
  (startexps', startargs) <- unzip <$> mapM checkArg startexps
  (arrexps', arrargs)     <- unzip <$> mapM checkSOACArrayArg arrexps
  fun'                    <- checkLambda fun $ startargs ++ arrargs
  let startt      = map subExpType startexps'
      intupletype = map argType arrargs
      funret      = lambdaType fun' $ map argType $ startargs ++ arrargs
  unless (startt `subtypesOf` funret) $
      bad $ TypeError pos $ "Accumulator is of type " ++ undefined startt ++
                            ", but reduce function returns type " ++ undefined funret ++ "."
  unless (intupletype `subtypesOf` funret) $
      bad $ TypeError pos $ "Array element value is of type " ++ undefined intupletype ++
                            ", but scan function returns type " ++ undefined funret ++ "."
  return $ Reduce ass' fun' (zip startexps' arrexps') pos

-- ScanT is exactly identical to ReduceT.  Duplicate for clarity
-- anyway.
checkExp (Scan ass fun inputs pos) = do
  let (startexps, arrexps) = unzip inputs
  ass' <- mapM (requireI [Basic Cert] <=< checkIdent) ass
  (startexps', startargs) <- unzip <$> mapM checkArg startexps
  (arrexps', arrargs)     <- unzip <$> mapM checkSOACArrayArg arrexps
  fun'                    <- checkLambda fun $ startargs ++ arrargs
  let startt      = map subExpType startexps'
      intupletype = map argType arrargs
      funret      = lambdaType fun' $ map argType $ startargs ++ startargs
  unless (startt `subtypesOf` funret) $
    bad $ TypeError pos $ "Initial value is of type " ++ undefined startt ++
                          ", but scan function returns type " ++ undefined funret ++ "."
  unless (intupletype `subtypesOf` funret) $
    bad $ TypeError pos $ "Array element value is of type " ++ undefined intupletype ++
                          ", but scan function returns type " ++ undefined funret ++ "."
  return $ Scan ass' fun' (zip startexps' arrexps') pos

checkExp (Filter ass fun arrexps pos) = do
  ass' <- mapM (requireI [Basic Cert] <=< checkIdent) ass
  (arrexps', arrargs) <- unzip <$> mapM checkSOACArrayArg arrexps
  fun' <- checkLambda fun arrargs
  let funret = lambdaType fun' $ map argType arrargs
  when (funret /= [Basic Bool]) $
    bad $ TypeError pos "FilterT function does not return bool."
  return $ Filter ass' fun' arrexps' pos

checkExp (Redomap ass outerfun innerfun accexps arrexps pos) = do
  ass' <- mapM (requireI [Basic Cert] <=< checkIdent) ass
  (arrexps', arrargs)  <- unzip <$> mapM checkSOACArrayArg arrexps
  (accexps', accargs)  <- unzip <$> mapM checkArg accexps
  (outerfun', retType) <- checkLambdaArg outerfun $ accargs ++ accargs

  innerfun' <- checkLambda innerfun $ accargs ++ arrargs

  let acct = map subExpType accexps'
      innerret = lambdaType innerfun' $ map argType $ accargs ++ arrargs
  unless (innerret `subtypesOf` acct) $
    bad $ TypeError pos $ "Initial value is of type " ++ undefined acct ++
          ", but redomapT inner reduction returns type " ++ undefined innerret ++ "."
  unless (retType `subtypesOf` acct) $
    bad $ TypeError pos $ "Initial value is of type " ++ undefined acct ++
          ", but redomapT outer reduction returns type " ++ undefined retType ++ "."

  return $ Redomap ass' outerfun' innerfun' accexps' arrexps' pos

checkSOACArrayArg :: SubExp -> TypeM (SubExp, Arg)
checkSOACArrayArg e = do
  (e', (t, dflow, argloc)) <- checkArg e
  case peelArray 1 t of
    Nothing -> bad $ TypeError argloc "SOAC argument is not an array"
    Just rt -> return (e', (rt, dflow, argloc))

checkIdent :: Ident -> TypeM Ident
checkIdent (Ident name t pos) = do
  vt <- lookupVar name pos
  t' <- checkAnnotation pos ("variable " ++ textual (baseName name)) t vt
  return $ Ident name t' pos

checkBinOp :: BinOp -> SubExp -> SubExp -> Type -> SrcLoc -> TypeM Exp
checkBinOp Plus e1 e2 t pos = checkPolyBinOp Plus [Real, Int] e1 e2 t pos
checkBinOp Minus e1 e2 t pos = checkPolyBinOp Minus [Real, Int] e1 e2 t pos
checkBinOp Pow e1 e2 t pos = checkPolyBinOp Pow [Real, Int] e1 e2 t pos
checkBinOp Times e1 e2 t pos = checkPolyBinOp Times [Real, Int] e1 e2 t pos
checkBinOp Divide e1 e2 t pos = checkPolyBinOp Divide [Real, Int] e1 e2 t pos
checkBinOp Mod e1 e2 t pos = checkPolyBinOp Mod [Int] e1 e2 t pos
checkBinOp ShiftR e1 e2 t pos = checkPolyBinOp ShiftR [Int] e1 e2 t pos
checkBinOp ShiftL e1 e2 t pos = checkPolyBinOp ShiftL [Int] e1 e2 t pos
checkBinOp Band e1 e2 t pos = checkPolyBinOp Band [Int] e1 e2 t pos
checkBinOp Xor e1 e2 t pos = checkPolyBinOp Xor [Int] e1 e2 t pos
checkBinOp Bor e1 e2 t pos = checkPolyBinOp Bor [Int] e1 e2 t pos
checkBinOp LogAnd e1 e2 t pos = checkPolyBinOp LogAnd [Bool] e1 e2 t pos
checkBinOp LogOr e1 e2 t pos = checkPolyBinOp LogOr [Bool] e1 e2 t pos
checkBinOp Equal e1 e2 t pos = checkRelOp Equal [Int, Real] e1 e2 t pos
checkBinOp Less e1 e2 t pos = checkRelOp Less [Int, Real] e1 e2 t pos
checkBinOp Leq e1 e2 t pos = checkRelOp Leq [Int, Real] e1 e2 t pos

checkRelOp :: BinOp -> [BasicType]
           -> SubExp -> SubExp
           -> Type -> SrcLoc
           -> TypeM Exp
checkRelOp op tl e1 e2 t pos = do
  e1' <- require (map Basic tl) =<< checkSubExp e1
  e2' <- require (map Basic tl) =<< checkSubExp e2
  _ <- unifySubExpTypes e1' e2'
  t' <- checkAnnotation pos (opStr op ++ " result") t $ Basic Bool
  return $ BinOp op e1' e2' t' pos

checkPolyBinOp :: BinOp -> [BasicType]
               -> SubExp -> SubExp -> Type -> SrcLoc
               -> TypeM Exp
checkPolyBinOp op tl e1 e2 t pos = do
  e1' <- require (map Basic tl) =<< checkSubExp e1
  e2' <- require (map Basic tl) =<< checkSubExp e2
  t' <- unifySubExpTypes e1' e2'
  t'' <- checkAnnotation pos (opStr op ++ " result") t t'
  return $ BinOp op e1' e2' t'' pos

sequentially :: TypeM a -> (a -> Dataflow -> TypeM b) -> TypeM b
sequentially m1 m2 = do
  (a, m1flow) <- collectDataflow m1
  (b, m2flow) <- collectDataflow $ m2 a m1flow
  occur $ usageOccurences m1flow `seqOccurences`
          usageOccurences m2flow
  return b

checkBinding :: SrcLoc -> [Ident] -> SrcLoc -> [Type] -> Dataflow
             -> TypeM (TypeM a -> TypeM a, [Ident])
checkBinding patloc pat tloc ts dflow
  | length pat == length ts = do
  (pat', idds) <-
    runStateT (zipWithM checkBinding' pat ts) []
  return (\m -> sequentially (tell dflow) (const . const $ binding idds m), pat')
  | otherwise =
  bad $ InvalidPatternError (Several pat) patloc (Several ts) tloc
  where checkBinding' (Ident name namet pos) t = do
          t' <- lift $
                checkAnnotation (srclocOf pat)
                ("binding of variable " ++ textual (baseName name)) namet t
          let t'' = subExpType $ Var $ Ident name t' pos
          add $ Ident name t'' pos
          return $ Ident name t'' pos

        add ident = do
          bnd <- gets $ find (==ident)
          case bnd of
            Nothing -> modify (ident:)
            Just (Ident name _ pos2) ->
              lift $ bad $ DupPatternError name (srclocOf ident) pos2

validApply :: [DeclType] -> [Type] -> Bool
validApply expected got =
  length got == length expected &&
  all id (zipWith subtypeOf (map toDecl got) expected)

type Arg = (Type, Dataflow, SrcLoc)

argType :: Arg -> Type
argType (t, _, _) = t

checkArg :: SubExp -> TypeM (SubExp, Arg)
checkArg arg = do (arg', dflow) <- collectDataflow $ checkSubExp arg
                  return (arg', (subExpType arg', dflow, srclocOf arg'))

checkLambdaArg :: Lambda -> [Arg]
               -> TypeM (Lambda, [Type])
checkLambdaArg lam args = do
  lam' <- checkLambda lam args
  let lamt = lambdaType lam' $ map argType args
  return (lam', lamt)

checkFuncall :: Maybe Name -> SrcLoc
             -> [DeclType] -> [DeclType] -> [Arg]
             -> TypeM ()
checkFuncall fname loc paramtypes _ args = do
  let argts = map argType args

  unless (validApply paramtypes argts) $
    bad $ ParameterMismatch fname loc
          (Right $ map (justOne . fromDecl) paramtypes) $
          map justOne argts

  forM_ (zip (map diet paramtypes) args) $ \(d, (t, dflow, argloc)) -> do
    maybeCheckOccurences $ usageOccurences dflow
    let occurs = [consumption (consumeArg t d) argloc]
    occur $ usageOccurences dflow `seqOccurences` occurs
  where consumeArg at Consume = aliases at
        consumeArg _  Observe = HS.empty

checkLambda :: Lambda -> [Arg] -> TypeM Lambda
checkLambda (Lambda params body ret loc) args = do
  (_, ret', params', body', _) <-
    noUnique $ checkFun (nameFromString "<anonymous>", ret, params, body, loc)
  if length params' == length args then do
    checkFuncall Nothing loc (map identType params') ret' args
    return $ Lambda params body' ret' loc
  else bad $ TypeError loc $ "Anonymous function defined with " ++ show (length params) ++ " parameters, but expected to take " ++ show (length args) ++ " arguments."
