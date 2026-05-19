module Main (main) where

import Test.HUnit
import Control.Monad.State (evalStateT)
import AST
import TypeChecker
import TypeCheckerF

run :: Expr -> Either String Type
run e = evalStateT (checker e) 0

runF :: Expr -> Either String Type
runF = checkerF

-- Bool literals
testTrue :: Test
testTrue = TestCase $ assertEqual "ETrue has type TBool" (Right TBool) (run ETrue)

testFalse :: Test
testFalse = TestCase $ assertEqual "EFalse has type TBool" (Right TBool) (run EFalse)

-- Nat literals
testZero :: Test
testZero = TestCase $ assertEqual "Zero has type TNat" (Right TNat) (run Zero)

testSuccZero :: Test
testSuccZero = TestCase $ assertEqual "Succ Zero has type TNat" (Right TNat) (run (Succ Zero))

testPredSuccZero :: Test
testPredSuccZero = TestCase $ assertEqual "Pred (Succ Zero) has type TNat" (Right TNat) (run (Pred (Succ Zero)))

testSuccNested :: Test
testSuccNested = TestCase $ assertEqual "Succ (Succ Zero) has type TNat" (Right TNat) (run (Succ (Succ Zero)))

-- IsZero
testIsZeroZero :: Test
testIsZeroZero = TestCase $ assertEqual "IsZero Zero has type TBool" (Right TBool) (run (IsZero Zero))

testIsZeroSucc :: Test
testIsZeroSucc = TestCase $ assertEqual "IsZero (Succ Zero) has type TBool" (Right TBool) (run (IsZero (Succ Zero)))

-- If expressions (well-typed)
testIfBoolBranches :: Test
testIfBoolBranches = TestCase $
  assertEqual "if true then true else false : TBool"
    (Right TBool)
    (run (If ETrue ETrue EFalse))

testIfNatBranches :: Test
testIfNatBranches = TestCase $
  assertEqual "if false then 0 else succ 0 : TNat"
    (Right TNat)
    (run (If EFalse Zero (Succ Zero)))

testIfCondIsZero :: Test
testIfCondIsZero = TestCase $
  assertEqual "if iszero 0 then 0 else succ 0 : TNat"
    (Right TNat)
    (run (If (IsZero Zero) Zero (Succ Zero)))

-- If expressions (ill-typed)
testIfNonBoolCond :: Test
testIfNonBoolCond = TestCase $
  case run (If Zero ETrue EFalse) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

testIfBranchMismatch :: Test
testIfBranchMismatch = TestCase $
  case run (If ETrue Zero EFalse) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

-- Succ / Pred on non-Nat (ill-typed)
testSuccBool :: Test
testSuccBool = TestCase $
  case run (Succ ETrue) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

testPredBool :: Test
testPredBool = TestCase $
  case run (Pred EFalse) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

-- IsZero on non-Nat (ill-typed)
testIsZeroBool :: Test
testIsZeroBool = TestCase $
  case run (IsZero ETrue) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

-- Var
testVarUnbound :: Test
testVarUnbound = TestCase $
  case run (Var "x") of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

-- Abs (well-typed)
testAbsIdentityBool :: Test
testAbsIdentityBool = TestCase $
  assertEqual "\\x:Bool. x : Bool -> Bool"
    (Right (TBool `TArrow` TBool))
    (run (Abs ("x", TBool) (Var "x")))

testAbsIdentityNat :: Test
testAbsIdentityNat = TestCase $
  assertEqual "\\x:Nat. x : Nat -> Nat"
    (Right (TNat `TArrow` TNat))
    (run (Abs ("x", TNat) (Var "x")))

testAbsConstant :: Test
testAbsConstant = TestCase $
  assertEqual "\\x:Bool. zero : Bool -> Nat"
    (Right (TBool `TArrow` TNat))
    (run (Abs ("x", TBool) Zero))

testAbsNested :: Test
testAbsNested = TestCase $
  assertEqual "\\x:Bool. \\y:Nat. x : Bool -> Nat -> Bool"
    (Right (TBool `TArrow` (TNat `TArrow` TBool)))
    (run (Abs ("x", TBool) (Abs ("y", TNat) (Var "x"))))

-- App (well-typed)
testAppIdentityBool :: Test
testAppIdentityBool = TestCase $
  assertEqual "(\\x:Bool. x) true : TBool"
    (Right TBool)
    (run (App (Abs ("x", TBool) (Var "x")) ETrue))

testAppIdentityNat :: Test
testAppIdentityNat = TestCase $
  assertEqual "(\\x:Nat. x) zero : TNat"
    (Right TNat)
    (run (App (Abs ("x", TNat) (Var "x")) Zero))

testAppReturnsBool :: Test
testAppReturnsBool = TestCase $
  assertEqual "(\\x:Nat. isZero x) zero : TBool"
    (Right TBool)
    (run (App (Abs ("x", TNat) (IsZero (Var "x"))) Zero))

-- App (ill-typed)
testAppNotAFunction :: Test
testAppNotAFunction = TestCase $
  case run (App ETrue EFalse) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

testAppArgMismatch :: Test
testAppArgMismatch = TestCase $
  case run (App (Abs ("x", TBool) (Var "x")) Zero) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

-- Let-polymorphism (well-typed)
-- Let-polymorphic id used at Bool.
testLetIdentityBool :: Test
testLetIdentityBool = TestCase $
  assertEqual "let id = \\x:a. x in id true : Bool"
    (Right TBool)
    (run (Let "id" (Abs ("x", TVar "a") (Var "x")) (App (Var "id") ETrue)))

-- Let-polymorphic id used at Nat.
testLetIdentityNat :: Test
testLetIdentityNat = TestCase $
  assertEqual "let id = \\x:a. x in id 0 : Nat"
    (Right TNat)
    (run (Let "id" (Abs ("x", TVar "a") (Var "x")) (App (Var "id") Zero)))

-- Let-polymorphic id reused at different types.
testLetPolyReuse :: Test
testLetPolyReuse = TestCase $
  assertEqual "let id = \\x:a. x in if (id true) then (id 0) else 0 : Nat"
    (Right TNat)
    (run (Let "id"
           (Abs ("x", TVar "a") (Var "x"))
           (If (App (Var "id") ETrue)
               (App (Var "id") Zero)
               Zero)))

-- Lambda-bound variables do not generalize (ill-typed)
-- Lambda-bound id should stay monomorphic.
testNoGeneralizationInAbs :: Test
testNoGeneralizationInAbs = TestCase $
  case run (Abs ("id", TVar "a" `TArrow` TVar "a")
              (If (App (Var "id") ETrue)
                  (App (Var "id") Zero)
                  Zero)) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

-- System F (explicit polymorphism)
-- System F identity type abstraction.
testFTypeAbsId :: Test
testFTypeAbsId = TestCase $
  assertEqual "TypeAbs id : forall a. a -> a"
    (Right (TForall "a" (TVar "a" `TArrow` TVar "a")))
    (runF (TypeAbs "a" (Abs ("x", TVar "a") (Var "x"))))

-- System F type application at Bool.
testFTypeAppBool :: Test
testFTypeAppBool = TestCase $
  assertEqual "(TypeAbs id) [Bool] true : Bool"
    (Right TBool)
    (runF (App (TypeApp (TypeAbs "a" (Abs ("x", TVar "a") (Var "x"))) TBool) ETrue))

-- System F rejects type app on non-forall.
testFTypeAppNotForall :: Test
testFTypeAppNotForall = TestCase $
  case runF (TypeApp (Abs ("x", TBool) (Var "x")) TBool) of
    Left _  -> return ()
    Right t -> assertFailure ("expected type error, got " ++ show t)

tests :: Test
tests = TestList
  [ TestLabel "ETrue"                testTrue
  , TestLabel "EFalse"               testFalse
  , TestLabel "Zero"                 testZero
  , TestLabel "Succ Zero"            testSuccZero
  , TestLabel "Pred (Succ Zero)"     testPredSuccZero
  , TestLabel "Succ (Succ Zero)"     testSuccNested
  , TestLabel "IsZero Zero"          testIsZeroZero
  , TestLabel "IsZero (Succ Zero)"   testIsZeroSucc
  , TestLabel "If bool branches"     testIfBoolBranches
  , TestLabel "If nat branches"      testIfNatBranches
  , TestLabel "If iszero cond"       testIfCondIsZero
  , TestLabel "If non-bool cond"     testIfNonBoolCond
  , TestLabel "If branch mismatch"   testIfBranchMismatch
  , TestLabel "Succ Bool"            testSuccBool
  , TestLabel "Pred Bool"            testPredBool
  , TestLabel "IsZero Bool"          testIsZeroBool
  , TestLabel "Var unbound"          testVarUnbound
  , TestLabel "Abs identity Bool"    testAbsIdentityBool
  , TestLabel "Abs identity Nat"     testAbsIdentityNat
  , TestLabel "Abs constant"         testAbsConstant
  , TestLabel "Abs nested"           testAbsNested
  , TestLabel "App identity Bool"    testAppIdentityBool
  , TestLabel "App identity Nat"     testAppIdentityNat
  , TestLabel "App returns Bool"     testAppReturnsBool
  , TestLabel "App not a function"   testAppNotAFunction
  , TestLabel "App arg mismatch"     testAppArgMismatch
  , TestLabel "Let id Bool"          testLetIdentityBool
  , TestLabel "Let id Nat"           testLetIdentityNat
  , TestLabel "Let id reuse"         testLetPolyReuse
  , TestLabel "No gen in Abs"        testNoGeneralizationInAbs
  , TestLabel "F type abs id"        testFTypeAbsId
  , TestLabel "F type app Bool"      testFTypeAppBool
  , TestLabel "F type app err"       testFTypeAppNotForall
  ]

main :: IO ()
main = do
  result <- runTestTT tests
  if errors result + failures result > 0
    then fail "Some tests failed."
    else return ()
