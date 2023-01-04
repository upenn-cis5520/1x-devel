{-
---
fulltitle: "Optional in class exercise: Freer Monad"
---
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module FreerExercise where

{-
This exercise is similar to the [Monad Transformer Exercise](TransExercise.html). It includes
the same problems, but solves them using the `freer-simple` library instead of with
monad transformers.

This exercise involves using the freer-simple library to extend a simple
imperative programming language, called `L`, with support for
*exceptions*. The language is a minimal subset of the `Lu` programming
language from your homework assignment, with the addition of `throw` and `try`
statements.

* For simplicity, we define the syntax of this extended language in a [separate
file](LSyntax.hs).

* The test case [try.l](try.l) demonstrates the syntax for exceptions in
  the extended language.

This exercise will give you practice with the `State`, `Throw`, and `Catch` (new!)
effects and the `StateC` and `ErrorC` monad transformers.
-}

import Control.Monad (when)
{-
As in the [Freer](Freer.html) module, we'll import most of the definitions
from the `freer-simple` library with the qualifier `Effect.`
-}

import Control.Monad.Freer (Eff, Member)
import qualified Control.Monad.Freer as Effect
import qualified Control.Monad.Freer.Error as Effect
import qualified Control.Monad.Freer.State as Effect
import Data.Map (Map)
import qualified Data.Map as Map
import LSyntax
  ( Block (..),
    Bop (..),
    Expression (..),
    Statement (..),
    Value (..),
    Var,
  )
import Test.HUnit
  ( Test (TestCase, TestList),
    assertFailure,
    runTestTT,
    (~:),
    (~?=),
  )

{-
State and Error effects
-----------------------

In this exercise, we'll be working with the following `Store` in the functions
below. This store records the value of all of the variables during execution.
-}

type Store = Map Var Value

{-
The `Effect.get` operation is a general purpose function for access the store.
We can give this function a slightly less generic type by fixing the
type of `Store` that we're working with.
-}

getStore :: (Member (Effect.State Store) effs) => Eff effs Store
getStore = Effect.get

{-
Similarly, updating the store also requires a monad that supports state effects.
-}

putStore :: (Member (Effect.State Store) effs) => Store -> Eff effs ()
putStore = Effect.put

{-
In the [Freer](Freer.html) module, you saw the `Error` effect, which was triggered by
the `throwError function`. In this exercise, you'll need to both throw and catch
errors.

Before, you saw that the `throwErrow` function can be used to signal an that an error occurred. Here, you'll need to use the type `Value` as your error information,
so we'll define a specialized version of that function.
-}

throwErrorValue :: (Member (Effect.Error Value) effs) => Value -> Eff effs a
throwErrorValue = Effect.throwError

{-
New today is the `catchError` function, that allows error recovery. The
`catchError` function takes a monadic computation of type `Eff effs a`, and if that computation throws an error, immediately calls the error handler
(of type `Value -> Eff effs a`) with the thrown value.

-}

catchErrorValue ::
  Member (Effect.Error Value) effs =>
  Eff effs a ->
  (Value -> Eff effs a) ->
  Eff effs a
catchErrorValue = Effect.catchError

{-
Expression Evaluator
--------------------

1. First, make sure that you understand how the expression evaluator works.
   Compared to the language of your homework, `L` lacks tables and most of
   the operators. Instead, it only includes global variables, arithmetic operators,
   ints, and `nil`.

-}

evalE :: (Member (Effect.State Store) effs) => Expression -> Eff effs Value
evalE (Var x) = do
  m <- getStore
  case Map.lookup x m of
    Just v -> return v
    Nothing -> return NilVal -- TODO: replace with `throwErrorValue (IntVal 0)`
evalE (Val v) = return v
evalE (Op2 e1 o e2) = evalOp2 o <$> evalE e1 <*> evalE e2

-- TODO: When you edit this function to use `throwErrorValue`, the type needs to
-- change.
evalOp2 Plus (IntVal i1) (IntVal i2) = IntVal (i1 + i2)
evalOp2 Minus (IntVal i1) (IntVal i2) = IntVal (i1 - i2)
evalOp2 Times (IntVal i1) (IntVal i2) = IntVal (i1 * i2)
evalOp2 Divide (IntVal _) (IntVal 0) = NilVal -- return nil for divide by 0
evalOp2 Divide (IntVal i1) (IntVal i2) = IntVal (i1 `div` i2)
evalOp2 _ _ _ = NilVal -- invalid args

{-
2. Next, modify `evalOp2` and `evalE` above so that they use `throwErrorValue` (defined above) to signal runtime errors

   - use code `IntVal 0` for undefined variables
   - use code `IntVal 1` in the case of divide by zero
   - use code `IntVal 2` in the case of invalid args to a numeric operator

NOTE: The types of these functions will be different once you make this modification.

Running and Testing the expression evaluator
------------------------------

To test the expression evaluator we have to pick an order to handle the `State` and
`Throw` effects.

Now we can run expressions that may throw errors!
-}

executeE :: Expression -> Store -> (Either Value Value, Store)
executeE e s = Effect.run $ Effect.runState s (Effect.runError comp)
  where
    comp = undefined -- replace this with `evalE e`

{-
We can display the errors nicely for experimentation in ghci with
this function. (The `display` function is defined at the end of the file).
-}

runE :: Expression -> IO ()
runE e = putStrLn $ display (fst (executeE e Map.empty))

{-
For example, try these out:
-}

-- "1 / 0"
-- >>> display (fst (executeE (Op2  (Val (IntVal 1)) Divide (Val (IntVal 0))) Map.empty))
-- "Uncaught exception: Divide by zero"

-- "1 / 1"
-- >>> display (fst (executeE (Op2  (Val (IntVal 1)) Divide (Val (IntVal 1))) Map.empty))
-- "Result: IntVal 1"

{-
We can also write tests that expect a particular execution to
raise a particular error.
-}

raisesE :: Expression -> Value -> Test
s `raisesE` v = case executeE s Map.empty of
  (Left v', _) -> v ~?= v'
  _ -> TestCase $ assertFailure "Error in raises"

{-
Make sure that your implementation above passes these tests.
-}

test_undefined :: Test
test_undefined =
  "undefined variable"
    ~: (Var "Y" `raisesE` IntVal 0)

divByZero :: Expression
divByZero = Op2 (Val (IntVal 1)) Divide (Val (IntVal 0))

test_divByZero :: Test
test_divByZero = "divide by zero" ~: divByZero `raisesE` IntVal 1

badPlus :: Expression
badPlus = Op2 (Val (IntVal 1)) Plus (Val NilVal)

test_badPlus :: Test
test_badPlus = "bad arg to plus" ~: badPlus `raisesE` IntVal 2

test_expErrors :: Test
test_expErrors =
  "undefined variable & division by zero"
    ~: TestList [test_undefined, test_divByZero, test_badPlus]

-- >>> runTestTT test_expErrors
-- Counts {cases = 3, tried = 3, errors = 0, failures = 0}

{-
Statement Evaluator
-------------------

3. Compare the types of `evalS` and `eval` below with the types in your
  homework assignment. (There is not much to do in this step except notice
  that changing the type of `evalE` changes the type of `evalS`.  You don't
  need to implement `Try` and `Throw` just yet.)
-}

evalCondition :: Value -> Bool
evalCondition (IntVal 0) = False -- since we don't have bools, use 0 & nil as false
evalCondition NilVal = False
evalCondition _ = True

-- type annotation intentionally not given

evalS ::
  (Member (Effect.Error Value) effs, Member (Effect.State Store) effs) =>
  Statement ->
  Eff effs ()
evalS (If e s1 s2) = do
  v <- evalE e
  if evalCondition v then eval s1 else eval s2
evalS (Assign x e) = do
  v <- evalE e
  m <- getStore
  putStore (Map.insert x v m)
evalS w@(While e ss) = do
  v <- evalE e
  when (evalCondition v) $ do
    eval ss
    evalS w
evalS (Try _ _ _) = error "evalS: unimplemented"
evalS (Throw _) = error "evalS: unimplemented"

-- type annotation intentionally not given
eval ::
  (Member (Effect.Error Value) effs, Member (Effect.State Store) effs) =>
  Block ->
  Eff effs ()
eval (Block ss) = mapM_ evalS ss

{-
4. Now finish this function for Statement execution. (Check out
  `executeE` for a hint.)
-}

execute :: Block -> Store -> (Either Value (), Store)
execute b st = undefined

{-
Try out your `execute` with this operation:
-}

runBlock :: Block -> String
runBlock block =
  let (r, s) = execute block Map.empty
   in display r ++ ",  Store: " ++ show s

{-
For example:
-}

-- >>> runBlock $ Block [While badPlus (Block [])]
-- "Uncaught exception: Invalid arguments to operator,  Store: fromList []"

{-
Test your functions with this helper
-}

raises :: Block -> Value -> Test
s `raises` v = case execute s Map.empty of
  (Left v', _) -> v ~?= v'
  _ -> TestCase $ assertFailure "Error in raises"

{-
and these tests:
-}

test_badWhile :: Test
test_badWhile = Block [While (Var "Y") (Block [])] `raises` IntVal 0

test_badIf :: Test
test_badIf = Block [If divByZero (Block []) (Block [])] `raises` IntVal 1

-- >>> runTestTT test_badWhile
-- Counts {cases = 1, tried = 1, errors = 0, failures = 0}

-- >>> runTestTT test_badIf
-- Counts {cases = 1, tried = 1, errors = 0, failures = 0}

{-
5. Add user-level exceptions

There are two new statement forms in this language. Extend the evaluator above
so that it can handle them.

- `Throw e` should evaluate the expression `e` and trigger an exception
  carrying the value of `e`

- `Try s x h` should execute the statement `s` and if, in the course
  of execution, an exception is thrown, then the exception value should
  be assigned to the variable `x` after which the *handler* statement
  `h` should be executed.

For example, this block is the abstract syntax for [try.l](try.l).
-}

tryExpr :: Block
tryExpr = Block [Assign "x" (Val (IntVal 0)), Assign "y" (Val (IntVal 1)), Try (Block [If (Op2 (Var "x") Plus (Var "y")) (Block [Assign "a" (Val (IntVal 100)), Throw (Op2 (Var "x") Plus (Var "y")), Assign "b" (Val (IntVal 200))]) (Block [])]) "e" (Block [Assign "z" (Op2 (Var "e") Plus (Var "a"))])]

-- >>> runBlock tryExpr
-- "Result: (),  Store: fromList [(\"a\",IntVal 100),(\"e\",IntVal 1),(\"x\",IntVal 0),(\"y\",IntVal 1),(\"z\",IntVal 101)]"

{-
Should print

       Result: ()
       Output Store: fromList [("a",IntVal 100),("e",IntVal 1),("x",IntVal 0),("y",IntVal 1),("z",IntVal 101)]

Displaying the results
-----------------------

There's nothing for you to do with this section other than make sure that you
understand how this code works.
-}

-- display the result of evaluation
display :: Show a => Either Value a -> String
display (Left v) = "Uncaught exception: " ++ displayExn v
display (Right v) = "Result: " ++ show v

-- decode an exception value
displayExn :: Value -> String
displayExn (IntVal 0) = "Undefined variable"
displayExn (IntVal 1) = "Divide by zero"
displayExn (IntVal 2) = "Invalid arguments to operator"
displayExn v = "Unknown error code: " ++ show v
