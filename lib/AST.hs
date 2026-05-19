module AST where

type Name = String

data Expr = ETrue
          | EFalse
          | If {cond :: Expr, exprThen :: Expr, exprElse :: Expr}
          | Zero
          | Succ Expr
          | Pred Expr
          | IsZero Expr
          | Var Name                  -- x               vars in Lambda Calculus
          | Abs (Name, Type) Expr     -- (\x:T . expr)   abstraction in Lambda Calculus
          | App Expr Expr             -- t1 t2           application in Lambda Calculus
          | Let Name Expr Expr        -- let x = e1 in e2
     deriving (Eq, Show)

data Value = VTrue
           | VFalse
           | VZero
           | VSucc Value
           | VAbs (Name, Type) Expr
     deriving (Eq, Show)

data Type = TBool
          | TNat
          | TVar Name
          | Type `TArrow` Type
     deriving (Eq, Show)

data Scheme = Forall [Name] Type
     deriving (Eq, Show)
