module TypeChecker where

import AST

import Control.Monad.State
import Control.Monad.Except (throwError)
import Data.List (nub, (\\))

-- The type checker uses Either for errors and StateT for fresh type variables.
-- The type environment is passed explicitly to keep substitution application clear.

type Env = [(Name, Scheme)]
type Err = Either String

-- State keeps the fresh type-variable counter.
type Res a = StateT Int Err a

type Subst = [(Name, Type)]

nullSubst :: Subst
nullSubst = []

-- Apply s1, then s2 (right-biased by s1 on conflicts).
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = [(v, applyType s1 t) | (v, t) <- s2] ++ s1

-- Replace type variables using a substitution.
applyType :: Subst -> Type -> Type
applyType s t = case t of
  TBool -> TBool
  TNat -> TNat
  TVar n -> case lookup n s of
    Just t' -> t'
    Nothing -> TVar n
  t1 `TArrow` t2 -> applyType s t1 `TArrow` applyType s t2

-- Do not substitute quantified variables in a scheme.
applyScheme :: Subst -> Scheme -> Scheme
applyScheme s (Forall vars t) = Forall vars (applyType s' t)
  where
    s' = filter (\(n, _) -> n `notElem` vars) s

-- Apply a substitution to every scheme in the environment.
applyEnv :: Subst -> Env -> Env
applyEnv s env = [(x, applyScheme s sc) | (x, sc) <- env]

-- Free type variables of a type.
ftvType :: Type -> [Name]
ftvType t = case t of
  TBool -> []
  TNat -> []
  TVar n -> [n]
  t1 `TArrow` t2 -> nub (ftvType t1 ++ ftvType t2)

-- Free type variables of a scheme (excluding quantified vars).
ftvScheme :: Scheme -> [Name]
ftvScheme (Forall vars t) = ftvType t \\ vars

-- Free type variables appearing anywhere in the environment.
ftvEnv :: Env -> [Name]
ftvEnv env = nub (concatMap (ftvScheme . snd) env)

-- Quantify all type vars that are not free in the environment.
generalize :: Env -> Type -> Scheme
generalize env t = Forall vars t
  where
    vars = ftvType t \\ ftvEnv env

-- Generate a fresh type variable (a0, a1, ...).
freshTVar :: Res Type
freshTVar = do
  n <- get
  put (n + 1)
  return (TVar ("a" ++ show n))

-- Replace quantified vars with fresh ones.
instantiate :: Scheme -> Res Type
instantiate (Forall vars t) = do
  fresh <- mapM (const freshTVar) vars
  let s = zip vars fresh
  return (applyType s t)

-- Bind a type variable, with occurs check.
bindVar :: Name -> Type -> Res Subst
bindVar u t
  | t == TVar u = return nullSubst
  | u `elem` ftvType t = throwError ("occurs check fails: " ++ u ++ " in " ++ show t)
  | otherwise = return [(u, t)]

-- Unify two types, producing a substitution.
unify :: Type -> Type -> Res Subst
unify t1 t2 = case (t1, t2) of
  (TBool, TBool) -> return nullSubst
  (TNat, TNat) -> return nullSubst
  (TVar u, t) -> bindVar u t
  (t, TVar u) -> bindVar u t
  (t11 `TArrow` t12, t21 `TArrow` t22) -> do
    s1 <- unify t11 t21
    s2 <- unify (applyType s1 t12) (applyType s1 t22)
    return (s2 `composeSubst` s1)
  _ -> throwError ("types do not unify: " ++ show t1 ++ " vs " ++ show t2)

-- Algorithm W (HM inference) returning a substitution and a type.
infer :: Env -> Expr -> Res (Subst, Type)
infer env expr = case expr of
  ETrue -> return (nullSubst, TBool)
  EFalse -> return (nullSubst, TBool)

  Zero -> return (nullSubst, TNat)

  Succ e -> do
    (s1, t1) <- infer env e
    s2 <- unify t1 TNat
    return (s2 `composeSubst` s1, TNat)

  Pred e -> do
    (s1, t1) <- infer env e
    s2 <- unify t1 TNat
    return (s2 `composeSubst` s1, TNat)

  IsZero e -> do
    (s1, t1) <- infer env e
    s2 <- unify t1 TNat
    return (s2 `composeSubst` s1, TBool)

  If e1 e2 e3 -> do
    (s1, t1) <- infer env e1
    s2 <- unify t1 TBool
    let env2 = applyEnv (s2 `composeSubst` s1) env
    (s3, t2) <- infer env2 e2
    let env3 = applyEnv (s3 `composeSubst` s2 `composeSubst` s1) env
    (s4, t3) <- infer env3 e3
    s5 <- unify (applyType s4 t2) t3
    let s = s5 `composeSubst` s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1
    return (s, applyType s t3)

  Var x -> case lookup x env of
    Nothing -> throwError ("variable not in scope: " ++ x)
    Just sc -> do
      -- Instantiation makes each use potentially monomorphic.
      t <- instantiate sc
      return (nullSubst, t)

  Abs (x, t1) e -> do
    -- Lambda annotations are treated as monomorphic.
    let env' = (x, Forall [] t1) : env
    (s1, t2) <- infer env' e
    return (s1, applyType s1 (t1 `TArrow` t2))

  App e1 e2 -> do
    (s1, t1) <- infer env e1
    let env2 = applyEnv s1 env
    (s2, t2) <- infer env2 e2
    -- Result type is fresh and then unified.
    tv <- freshTVar
    s3 <- unify (applyType s2 t1) (t2 `TArrow` tv)
    let s = s3 `composeSubst` s2 `composeSubst` s1
    return (s, applyType s tv)

  Let x e1 e2 -> do
    (s1, t1) <- infer env e1
    let env1 = applyEnv s1 env
    -- Let is the generalization point in HM.
    let sc = generalize env1 t1
    (s2, t2) <- infer ((x, sc) : env1) e2
    let s = s2 `composeSubst` s1
    return (s, applyType s t2)

checker :: Expr -> Res Type
checker expr = do
  (s, t) <- infer [] expr
  return (applyType s t)
