module TypeCheckerF where

import AST

import Control.Monad.Except (throwError)

-- System F type checker (explicit type abstraction/application).

type TypeEnv = [Name]
type TermEnv = [(Name, Type)]
type Err = Either String

-- Check that a type is well-formed under a type environment.
checkType :: TypeEnv -> Type -> Err ()
checkType tenv t = case t of
  TBool -> return ()
  TNat -> return ()
  TVar a ->
    if a `elem` tenv
      then return ()
      else throwError ("unbound type variable: " ++ a)
  TForall a t1 -> checkType (a : tenv) t1
  t1 `TArrow` t2 -> checkType tenv t1 >> checkType tenv t2

-- Substitute a type for a type variable.
substType :: Name -> Type -> Type -> Type
substType a t target = case target of
  TBool -> TBool
  TNat -> TNat
  TVar b -> if a == b then t else TVar b
  TForall b t1 -> if a == b then TForall b t1 else TForall b (substType a t t1)
  t1 `TArrow` t2 -> substType a t t1 `TArrow` substType a t t2

-- Type checker for System F terms (explicit type abstraction/application).
inferF :: TypeEnv -> TermEnv -> Expr -> Err Type
inferF tenv env expr = case expr of
  ETrue -> return TBool
  EFalse -> return TBool

  Zero -> return TNat

  Succ e -> do
    t <- inferF tenv env e
    if t == TNat then return TNat else throwError ("succ expects Nat, got " ++ show t)

  Pred e -> do
    t <- inferF tenv env e
    if t == TNat then return TNat else throwError ("pred expects Nat, got " ++ show t)

  IsZero e -> do
    t <- inferF tenv env e
    if t == TNat then return TBool else throwError ("isZero expects Nat, got " ++ show t)

  If e1 e2 e3 -> do
    t1 <- inferF tenv env e1
    if t1 /= TBool
      then throwError ("condition of if must be Bool, got " ++ show t1)
      else do
        t2 <- inferF tenv env e2
        t3 <- inferF tenv env e3
        if t2 == t3
          then return t2
          else throwError ("then/else branches have different types: " ++ show t2 ++ " vs " ++ show t3)

  Var x -> case lookup x env of
    Nothing -> throwError ("variable not in scope: " ++ x)
    Just t -> return t

  Abs (x, t1) e -> do
    checkType tenv t1
    t2 <- inferF tenv ((x, t1) : env) e
    return (t1 `TArrow` t2)

  App e1 e2 -> do
    t1 <- inferF tenv env e1
    t2 <- inferF tenv env e2
    case t1 of
      t11 `TArrow` t12 ->
        if t2 == t11
          then return t12
          else throwError ("argument type mismatch: expected " ++ show t11 ++ ", got " ++ show t2)
      _ -> throwError ("expected a function type, got " ++ show t1)

  TypeAbs a e -> do
    t <- inferF (a : tenv) env e
    return (TForall a t)

  TypeApp e tArg -> do
    checkType tenv tArg
    t <- inferF tenv env e
    case t of
      TForall a tBody -> return (substType a tArg tBody)
      _ -> throwError ("expected a forall type, got " ++ show t)

  Let x e1 e2 -> do
    -- Let is monomorphic in the System F checker.
    t1 <- inferF tenv env e1
    inferF tenv ((x, t1) : env) e2

checkerF :: Expr -> Err Type
checkerF expr = inferF [] [] expr
