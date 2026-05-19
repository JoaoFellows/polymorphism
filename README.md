# Lambda Polymorphism Extensions

This repository now includes two polymorphism flavors:

- Hindley-Milner (HM) with let-polymorphism and implicit instantiation.
- System F with explicit type abstraction and type application.

## AST additions

The core syntax was extended to support polymorphism:

- Expr:
  - Let Name Expr Expr
  - TypeAbs Name Expr
  - TypeApp Expr Type
- Type:
  - TVar Name
  - TForall Name Type
- Scheme:
  - Forall [Name] Type

## HM type checker (TypeChecker)

HM keeps annotated lambdas and adds:

- Substitutions and unification (applyType, unify, composeSubst).
- Free type variables and generalization (ftvType, generalize).
- Instantiation on variable use (instantiate).
- Let-polymorphism as the only generalization point.
- TypeAbs and TypeApp are rejected in HM.

## System F type checker (TypeCheckerF)

System F is explicit:

- Type abstraction: TypeAbs a e gives type forall a. T.
- Type application: TypeApp e T applies a forall type.
- Type well-formedness checks (checkType) and type substitution (substType).
- Let is monomorphic in this checker.

## Tests

Polymorphism tests were added to test/Main.hs:

- HM let-polymorphism: id used at Bool and Nat, reuse in the same let.
- HM non-generalization under lambda.
- System F: type abstraction, type application, and a negative case.

## Run tests

```bash
cabal test
```
