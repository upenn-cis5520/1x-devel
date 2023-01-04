{-# LANGUAGE DataKinds #-}
{-
---
fulltitle: "Optional module: The Freer Monad"
---

This module is an alternative approach to Monad Transformers, as shown in the [Transformers](Transformers.html) module. It is optional material, intended to demonstrate recent work in using Haskell's type system to track effectful code. It also introduces (at the very end) the concept of a "Freer Monad" --- the essence of the monad type class and a way to describe computation abstractly. This module is based on and uses the same running examples as in the `Transformers` module for easy comparison.

This module relies on the
[`freer-simple`](https://hackage.haskell.org/package/freer-simple) library,
a mechanism for the flexible tracking and interpretation of effects.
Like monad transformers, the `freer-simple` library supports the use of multiple effects at once, and allows effectful code to be interpreted in different ways.
However, this approach is a bit more difficult to use as it is based on GADTs and
type-level programming.

Preliminaries
-------------

Besides the usual language extensions specified in the associated
cabal file, we'll also need to be able to work with GADTs, DataKinds and
be a little more flexible about our instance declarations.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module Freer where

{-
This module uses definitions from the `freer-simple` library. A few of them
we will import straight out, but the ones related to the `Either` monad and the
`State` monad we'll import with qualification so that it is clear where they are
defined.
-}

{-
We'll also use our old friend the `State` monad, that we defined previously [`State`](../09-state/State.html)
and is included in this project for convenience. Because some of the names in the `freer-simple` library above
conflict with the names in the `State` module, we'll also import this one qualified by the prefix `StateMonad`.
-}

{-
For comparison, we'll also import operations for mutable data and for exceptions in the IO monad.
-}

import Control.Exception (Exception, throwIO)
import Control.Monad (ap)
import Control.Monad.Freer (Eff, LastMember, Member)
import qualified Control.Monad.Freer as Effect
import qualified Control.Monad.Freer.Error as Effect
import qualified Control.Monad.Freer.State as Effect
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.IORef as IO (IORef, newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import qualified State as StateMonad

{-
Motivating example: How do we use *multiple* monads at once?
============================================================

Today, we will see how monads can be used to write (and compose)
simple evaluators for programming languages.

Let's look at a simple language of division expressions.
-}

data Expr
  = Val Int
  | Div Expr Expr
  deriving (Show)

{-
Our first evaluator is *unsafe*.
-}

eval :: Expr -> Int
eval (Val n) = n
eval (Div x y) = eval x `div` eval y

{-
Here are two terms that we will use as running examples.
-}

ok :: Expr
ok =
  (Val 1972 `Div` Val 2)
    `Div` Val 23

err :: Expr
err =
  Val 2
    `Div` ( Val 1
              `Div` (Val 2 `Div` Val 3)
          )

{-
The first evaluates properly and returns a valid answer, while the
second fails during execution with a divide-by-zero error.
-}

-- >>> eval ok
-- 42

-- >>> eval err
-- divide by zero

{-
This `eval` function is not very good because a
divide-by-zero error stops the *whole* evaluator. And, there is nothing to
do about it: we can't catch the error.

Of course, one way to fix the problem is to detect the error and then
continue with a default value (such as 0).
-}

evalDefault :: Expr -> Int
evalDefault (Val n) = n
evalDefault (Div x y) =
  let m = evalDefault y
   in if m == 0 then 0 else evalDefault x `div` m

{-
But, no one likes this solution. It leads to buggy code.

Error Handling Via the `Either` Monad
-------------------------------------

A much better approach is to use the `Either` type to treat the failure case more
gently. This type holds two possible values, and those values could have different types.

~~~~~~~~{.haskell}
     data Either s a = Left s | Right a
~~~~~~~~

If we update the result type of our evaluator to be `Either String Int`, then
we can use a `Left s` result to mean that an error happened somewhere, where
`s` is an error message, while a `Right n` result means that evaluation
succeeded yielding `n`.

You've seen already that the `Maybe` monad can let us conveniently detect and react to
errors. The `Either` type can be made to work similarly. In practice, using this
monad is like working with real exception mechanism where we can say `throwError X`
(`X` is a description of what went wrong) and this error information would would percolate
up to the top and tell us what the problem was.

Here is the definition of the `Either s` monad, which is a generalization of
the `Maybe` monad.  Note that the instance is for `Either s` not
`Either s a` -- the two type parameters to `Either` are not treated symmetrically.
The first must be the type of error values that we can throw (we'll use `String`s today)
and the second is the computation type for the monad.

~~~~~~~~~{.haskell}

   instance Monad (Either s) where

        (>>=)  :: Either s a -> (a -> Either s b) -> Either s b
        Right x >>= f = f x
        Left s  >>= _ = Left s

        return :: a -> Either s a
        return   = Right

~~~~~~~~~

Now rewrite the `eval` function using this `Error` (and the monadic do notation).
For convenience, you can use the helper function `errorS`
to generate the error string when the evaluator detects a division by 0.
In such case, the result should be `Left (errorS vx vy)` where `vx` and `vy` are
the values that are to be divided.
-}

-- | Format an error string
errorS :: Show a => a -> a -> String
errorS y m = "Error dividing " ++ show y ++ " by " ++ show m

evalEx :: Expr -> Either String Int
evalEx (Val n) = return n
evalEx (Div x y) = undefined

{-
Your implementation should return `Right 42` for the `ok` term
and `Left` with an informative string for `err`.
-}

-- >>> evalEx ok
-- Right 42

-- >>> evalEx err
-- Left "Error dividing Val 1 by Div (Val 2) (Val 3)"

{-
Counting Operations Using the State Monad
-----------------------------------------

Next, let's stop being paranoid about errors and instead try to do
some *profiling*. Let's imagine that the `div` operator is very
expensive, and that we would like to *count* the number of divisions
that are performed while evaluating a particular expression.

As you might imagine, our old friend the state monad is going to be
just what we need here! The type of store that we'd like to use is
just the count of number of division operations, and we can store that
in an `Int`.  The state monad we're going to use is defined in the
module [`State`](11-transformers/State.html), imported above. We've
qualified every definition in this module by `State` so that you can tell
where it is from.

We'll need a way of incrementing the counter:
-}

tickStateMonad :: StateMonad.State Int ()
tickStateMonad = do
  x <- StateMonad.get -- use get and put from the state monad
  StateMonad.put (x + 1)

{-
Now we can write a *profiling* evaluator,
-}

evalSt :: Expr -> StateMonad.State Int Int
evalSt (Val n) = return n
evalSt (Div x y) = do
  m <- evalSt x
  n <- evalSt y
  tickStateMonad
  return (m `div` n)

{-
and observe it at work
-}

goSt :: Expr -> String
goSt e = "value: " ++ show x ++ ", count: " ++ show s
  where
    (x, s) = StateMonad.runState (evalSt e) 0 :: (Int, Int)

-- >>> goSt ok
-- "value: 42, count: 2"

{-
But... alas!  To get the profiling, we threw out the nifty error
handling that we had put in earlier!!
-}

-- >>> goSt err
-- divide by zero

{-
Freer Effects: Working with multiple effects
============================================

So, at the moment, it seems that monads can do many things, but only *one
thing at a time*---you can either use a monad to do the error-management
plumbing *or* to do the state-manipulation plumbing, but not both at once.
Is it too much ask for both? I guess we could write a
*mega-state-and-exception* monad that supports both sets of operations, but
that doesn't sound fun!  Especially since, if we later decide to add yet
another feature, then we would have to make up yet another mega-monad.

So we will take a different approach.

This approach requires a little more work up-front (most of which is done
already in well-designed libraries), but after that we can add new
features in a modular manner.

Step 1: A monad parameterized by its effects
--------------------------------------------

The first step to being able to compose effects is to have a flexible way
to describe the effects of a monadic computation.

The `Eff` type, from `freer-simple`, is a monad that can do just this.
-}

-- >>> :kind Eff
-- Eff :: [Type -> Type] -> Type -> Type

{-
The first argument to `Eff` is a type-level list where every element
of this list describes the effects that could occur in a monadic
computation of this type. For example, the library includes an
effect `Effect.Error` so the type `Eff '[Effect.Error String] Int` describes a
computation that either returns an `Int` or could throw an error
(with an error value of type `String`). This type is similar to
the type `Either String Int`. Furthermore, the library also includes
an effect `Effect.State` so the type `Eff '[Effect.State Int] Int` describes a
computation that either returns an `Int` and accesses a store of type `Int`,
similar to the type `State Int Int`.

However, for flexibility, instead of giving the complete list of effects
that a computation uses, we can also talk about part of this list.
For example, in the `freer-simple` library, the `throwError` function
has the following type:

~~~~~
Effect.throwError :: Member (Effect.Error e) effs => e -> Eff effs a
~~~~~

This type is a bit complicated to read at first, but let's walk through it.
The `throwError` function takes an error value of type `e` (e.g. `String` like
we used above) to signal the error. The result type is `Eff effs a` where `a`
is polymorphic --- in other words, we can throw an error when any result is
expected.

The type `Eff effs` is also polymorphic. We don't know the list of effects.
However, the constraint on this type (the part before `=>`) says that the
effect `Effect.Error e` must be contained in this list.

Similarly, the `freer-simple` library includes operations for working with
state.  In this case, using either `get` or `put` is
valid when the monad `Eff` has the `Effect.State s` effect in its list,
where the type parameter `s` is the type of the store.

~~~~~~
Effect.get :: Member (Effect.State s) effs => Eff effs s

Effect.put :: Member (Effect.State s) effs => s -> Eff effs ()
~~~~~~

With these functions, can redefine the ticking operation to work for
*any* `Eff` monad that uses `State` effects.
-}

tickStateEffect :: Member (Effect.State Int) eff => Eff eff ()
tickStateEffect = do
  (x :: Int) <- Effect.get
  Effect.put (x + 1)

{-
There is a cost to this generality though. We need to tell GHC what type
of store we are working with. The easiest way to do so is with a type
annotation for the result of `get`.

Step 2: Using the `Eff` Monad
-----------------------------

Armed with these two effects, we can write our exception-throwing,
step-counting evaluator quite easily:
-}

evalMega ::
  ( Member (Effect.State Int) eff,
    Member (Effect.Error String) eff
  ) =>
  Expr ->
  Eff eff Int
evalMega (Val n) = return n
evalMega (Div x y) = do
  n <- evalMega x
  m <- evalMega y
  if m == 0
    then Effect.throwError $ errorS n m
    else do
      tickStateEffect
      return (n `div` m)

{-
Note that this code is simply the combination of the two evaluators from before -- we
use the error handling from `evalEx` and the profiling from `evalSt`.

There are two other, less polymorphic, types we could have given to `evalMega` above.
In the next section, we explain why we chose the type that we did.

Step 3: Handling Effects
------------------------

We can run the `evalMega` function by telling it how to handle each
of its effects, one by one. The `freer-simpler` library gives us functions
for that purpose.
-}

-- >>> :t Effect.runState
-- Effect.runState :: s -> Eff (State s : effs) a -> Eff effs (a, s)

{-
The type of the `runState` function says that it needs an initial store (of type `s`),
and a computation that reads and writes to that store. This function returns
a new computation that no longer has such effects---the `State` part of the
effect list is gone in the result. The result type `(a,s)` adds the final store
to the result of the computation.
-}

-- >>> :t Effect.runError
-- Effect.runError :: Eff (Error e : effs) a -> Eff effs (Either e a)

{-
The `runError` function handles error effects in the computation. The `Either` in
the result type tells whether the computation threw an error or not.

Finally, the library provides a way to get the final value out of a monadic
computation that has no effects. If the list of effects in the `Eff` type is
empty, then you can `run` the monad to get its value.
-}

-- >>> :t Effect.run
-- Effect.run :: Eff '[] a -> a

{-
But, we have a choice when we are handling the effects from `evalMega`.
We can handle the state effects first (see `goExSt`) or we can handle
the error effects first (see `goStEx`).

We get this flexibility because `evalMega` doesn't care what order the
effects appear in the list. Its type only says that whatever this list is,
it must contain both `Effect.State Int` and `Effect.Error String`. So this
list could be `'[Effect.State Int, Effect.Error String]` or it could be
`'[Effect.Error String, Effect.State Int]`. The choice that we make
determines the what type of result we get from processing the effects.

-}

goExSt :: Expr -> String
goExSt e =
  (evalMega e :: Eff '[Effect.State Int, Effect.Error String] Int)
    & Effect.runState 0 -- the & operator is a reverse $
    & Effect.runError -- using it we can chain togther
    & Effect.run -- the sequence of run functions nicely
    & format
  where
    format :: Either String (Int, Int) -> String
    format (Left s) = "Raise: " ++ s
    format (Right (v, cnt)) =
      "Count: " ++ show cnt ++ "  "
        ++ "Result: "
        ++ show v

goStEx :: Expr -> String
goStEx e =
  (evalMega e :: Eff '[Effect.Error String, Effect.State Int] Int)
    & Effect.runError -- this one handles the error effects
    & Effect.runState 0 -- before handling the state effects
    & Effect.run
    & format
  where
    format :: (Either String Int, Int) -> String
    format (r, cnt) =
      "Count: " ++ show cnt ++ "  "
        ++ case r of
          Left s -> "Raise: " ++ s
          Right v -> "Result: " ++ show v

{-
Not only does the choice affect our result type, but it also impacts the
behavior of the computation. When everything works, we get the same answer.
But look what happens if we try to divide by zero!
-}

-- >>> goExSt ok
-- "Count: 2  Result: 42"

-- >>> goExSt err
-- "Raise: Error dividing 1 by 0"

-- >>> goStEx ok
-- "Count: 2  Result: 42"

-- >>> goStEx err
-- "Count: 1  Raise: Error dividing 1 by 0"

{-
IO Effects
==========

What if we *want* to use the `IO` monad in combination with the `Eff` monad?
The `freer-simple` library includes the following (overloaded) function,
that says that if `IO` is recorded as the last effect in the list,
then it is possible to "lift" IO operations directly into the `Eff` monad.

~~~~~~~~~~~~~~~~~~~~~~~
liftIO :: LastMember IO eff => IO a -> Eff eff a
~~~~~~~~~~~~~~~~~~~~~~~

For example, suppose we want to add a "tracing" like effect to
our code. Then, right before we call the `tickStateEffect` function
we can use `liftIO` to add a call to print.
-}

evalIO ::
  ( Member (Effect.State Int) eff,
    Member (Effect.Error String) eff,
    LastMember IO eff
  ) =>
  Expr ->
  Eff eff Int
evalIO (Val n) = return n
evalIO (Div x y) = do
  n <- evalIO x
  m <- evalIO y
  if m == 0
    then Effect.throwError $ errorS n m
    else do
      liftIO $ print "I'm going to divide now!"
      tickStateEffect
      return (n `div` m)

{-
Running this computation means that we need to add IO to the list of effects,
and then use `Effect.runM` when we process this last effect. Unlike `Effect.run`,
the `runM` function returns its result in the `IO` monad. That changes the
overall type of the evaluator.
-}

goIOStEx :: Expr -> IO String
goIOStEx e =
  (evalIO e :: Eff '[Effect.Error String, Effect.State Int, IO] Int)
    & Effect.runError
    & Effect.runState 0
    & Effect.runM
    <&> format -- <&> is `flip fmap`
  where
    format :: (Either String Int, Int) -> String
    format (r, cnt) =
      "Count: " ++ show cnt ++ "  "
        ++ case r of
          Left s -> "Raise: " ++ s
          Right v -> "Result: " ++ show v

{-
With this modification, we can see the output from `print` if we call the
function inside ghci.

            ghci> goIOStEx ok
            "I'm going to divide now!"
            "I'm going to divide now!"
            "Count: 2  Result: 42"

            ghci> goIOStEx err
            "I'm going to divide now!"
            "Count: 1  Raise: Error dividing 1 by 0"

Alternative Interpretations of Effects
=====================================

The `Effect.runState` function interprets `State` effects using store
passing. Internally, the store type is passed through the computation,
just as in our version of the `State` monad.

However, the `freer-effects` library is more flexible than that. When
defining an effectful function, like `evalMega`, the library records the
effects of the function using the `Eff` monad, but doesn't give them an
interpretation until the call to `runState`.

Let's take a look at what the `State` effect looks like. In the library,
this data structure is defined with the following GADT.

~~~~~~~~
data State (s :: Type) (r :: Type) where
   Get :: State s s
   Put :: s -> State s ()
~~~~~~~~

So a state "effect" is only a tag (`Get` or `Put`) that says that the function wants to
access or update the store. When you define functions with the `Eff` monad, such
as with `evalMega` you are marking places where `Get` and `Put` occurs during the
computation, but no store passing is actually happening (yet).

What this means is that it is possible to interpret the state effects in the
computation in multiple ways.

For example, instead of using the state monad, we could instead use the IO monad to
interpret state effects. We do this in two stages.
First, we use the library's `interpretM` function to convert
converts all uses of `Get` and `Put` to calls to `readIORef` and `writeIORef`.
(If you've forgotten how IORefs work, see the short description at the beginning of the
StateMonad lecture.) The `interpretM` function works for any effect
(like `Effect.State`) as long as the targetted monad is the last effect in the
list of effects.
-}

interpretIO ::
  (LastMember IO effs) =>
  IORef Int ->
  Eff (Effect.State Int ': effs) a ->
  Eff effs a
interpretIO ref = Effect.interpretM (stateAsIO ref)

stateAsIO :: IORef s -> Effect.State s a -> IO a
stateAsIO ref Effect.Get = IO.readIORef ref
stateAsIO ref (Effect.Put s) = IO.writeIORef ref s

{-
Second, we use this effect reinterpretation when we interpret all of the effects
of a computation, like `evalMega`. Because we can't really escape the "IO" monad,
it has to be the last effect in the list: and instead of using `Effect.run`, which
returns a pure value, we use `Effect.runM` that converts a computation of type
`Eff IO Int` to one of type `IO Int`.
-}

goIOEx :: Expr -> IO String
goIOEx e = do
  ref <- IO.newIORef 0 -- allocate ref for the store
  v <-
    (evalMega e :: Eff '[Effect.State Int, Effect.Error String, IO] Int)
      & interpretIO ref -- interpret Get/Put as readIORef/writeIORef
      & Effect.runError -- interpret throwError
      & Effect.runM -- run IO effects
  cnt <- IO.readIORef ref -- read the final value of the store
  return (format (v, cnt))
  where
    format :: (Either String Int, Int) -> String
    format (r, cnt) =
      "Count: " ++ show cnt ++ "  "
        ++ case r of
          Left s -> "Raise: " ++ s
          Right v -> "Result: " ++ show v

-- >>> goIOEx ok
-- "Count: 2  Result: 42"
{-

-}

-- >>> goIOEx err
-- "Count: 1  Raise: Error dividing 1 by 0"

{-
Behind the scenes
=================

So far, you have seen how you can use the `Eff` monad in your code.
How does the `Eff` monad and the `freer-simple` library actually work?

You don't need to understand this last bit in order to use the library,
but its design is based on some incredible ideas that we'll sketch below.

The library itself is optimized, but in this section, we'll show you how
to define the `Eff` type, show that it is a monad, and implement operations
such as `get`, `put` and `runState.`

The key idea of this library design is that the Eff type is a variant of
a *Freer* monad. This structure looks something like the type `Freer` below.
(For simplicity, in this section, we'll parameterize this monad type by
a single effect instead of a list of effects. Managing this list of effects is
another issue solved by the `freer-simple` library.)

The `Freer` type has two constructors: one for pure values (`Pure`) and one for
effectful computations (`Impure`).
-}

data Freer (eff :: Type -> Type) (a :: Type) where
  Pure :: a -> Freer eff a
  Impure :: eff b -> (b -> Freer eff a) -> Freer eff a

{-
If you look closely at the type of `Impure`, you'll see that the type
parameter `b` does not appear in the result type. This means that this
variable is unconstrained. The `Impure` constructor can carry an effect
of type `eff b` as long as there is some "continuation" function that
knows what to do with the `b` in the rest of the computation.

This monad is called "Freer" because it is very close to capturing
the essence of what it means to be a monad. These two constructors
correspond to the return and bind operations of the monad. In fact,
`return` is implemented directly as `Pure`. For `bind', the implementation
is similar to `Impure`, however, the definition of `(>>=)` does a
little processing to simplify the definition according to the monad
laws. (Compare the first case of `>>=` below to the left identity law.)
-}

deriving instance (Functor (Freer eff))

instance Applicative (Freer eff) where
  pure = Pure
  (<*>) = ap

instance Monad (Freer eff) where
  Pure x >>= k = k x
  Impure u q >>= k = Impure u (\b -> q b >>= k)

{-
A key operation is the `runM` function, that interprets the effect `eff`
into some monad `m`, given some effect interpretation function `f`.
-}

runM :: Monad m => (forall b. eff b -> m b) -> Freer eff a -> m a
runM f (Pure x) = return x
runM f (Impure m k) = do
  v <- f m
  runM f (k v)

{-
Freer and State effects
-----------------------

Now let's use the `Freer` monad with the `State` effect. Recall, the definition
of the `State` effect above as a GADT with two constructors, `Get` and `Put`.
To implement the `get` and `put` operations we need to just inject these
constructors into the `Freer` data structure using the `send` operation.
-}

get :: Freer (Effect.State s) s
get = send Effect.Get

put :: s -> Freer (Effect.State s) ()
put v = send (Effect.Put v)

{-
The `send` operation works for any effect. It tags the computation as
impure and then does nothing else.
-}

send :: eff a -> Freer eff a
send x = Impure x Pure

{-
On the other end, we need to say how to interpret the `Get` and `Put`
tags in the monadic computation using the standard `State` monad. We do
this by construction the following effect interpretation function:
-}

stateAsState :: Effect.State s a -> StateMonad.State s a
stateAsState Effect.Get = StateMonad.get
stateAsState (Effect.Put s) = StateMonad.put s

{-
Finally, let's see the `Freer` monad in action! We can define an evaluator
for our simple language (like `evalSt` above):
-}

evalFreer :: Expr -> Freer (Effect.State Int) Int
evalFreer (Val n) = return n
evalFreer (Div x y) = do
  m <- evalFreer x
  n <- evalFreer y
  x <- get
  put (x + 1)
  return (m `div` n)

{-
And then use `runState` and `runM` to execute this evaluator using
the interpretation into the `State`` monad.
-}

-- >>> StateMonad.runState (runM stateAsState (evalFreer ok)) 0
-- (42,2)

{-
But, we can also execute this evaluator by providing a different
effect interpretation function, i.e. `stateAsIO` above.
-}

runIO :: IO (Int, Int)
runIO = do
  ref <- IO.newIORef 0
  v <- runM (stateAsIO ref) (evalFreer ok)
  cnt <- IO.readIORef ref
  return (v, cnt)

-- >>> runIO
-- (42,2)

{-
Freer and Error effects
-----------------------
For simplicity, we haven't designed a way to use more than one effect at a
time with `Freer`. The `freer-simple` library does that using type-level
lists and class constraints such as `Member`. We won't do that sort of
encoding today.

However, we will show that this implementation is flexible enough to
do different kinds of effects, even if it cannot handle them all simultaneously.

The error effect, `Effect.error` is defined in the library with the following
new type. This effect corresponds only to locations where we might throw an
error.

~~~~~~~~~~~~~~~~~~
newtype Error e r where
    Error :: e -> Error e r
~~~~~~~~~~~~~~~~~~

We can define an error throwing function by just sending the error effect
to the `Freer` monad.
-}

throwError :: s -> Freer (Effect.Error s) a
throwError s = send (Effect.Error s)

{-
With this function, we can write code that (potentially) throws errors.
-}

evalError :: Expr -> Freer (Effect.Error String) Int
evalError (Val n) = return n
evalError (Div x y) = do
  vx <- evalError x
  vy <- evalError y
  if vy == 0 then throwError (errorS vx vy) else return (vx `div` vy)

{-
To run this evaluator, we need to provide an effect interpretation
for the error effect. To interpret it into the `Either` monad, we
just use `Left`.
-}

errorAsEither :: Effect.Error s a -> Either s a
errorAsEither (Effect.Error s) = Left s

-- >>>  runM errorAsEither (evalError ok)
-- Right 42

-- >>>  runM errorAsEither (evalError err)
-- Left "Error dividing 1 by 0"

{-
Or, we could interpret it into the `Maybe` monad,
this time using `Nothing` (though we lose the
error string in the process).
-}

errorAsMaybe :: Effect.Error s a -> Maybe a
errorAsMaybe (Effect.Error s) = Nothing

-- >>>  runM errorAsMaybe (evalError ok)
-- Just 42

-- >>>  runM errorAsMaybe (evalError err)
-- Nothing

{-
Or, we could interpret it into the `IO` monad,
this time using IO based execeptions. These can
be thrown with the `throwIO` function.
-}

-- declare that we will use strings as exception values
instance Exception String

-- interpret Errors in the IO monad using throwIO
errorAsIO :: Effect.Error String a -> IO a
errorAsIO (Effect.Error s) = throwIO s

{-
Now, run the evaluator in the IO monad:
-}

-- >>> runM errorAsIO (evalError ok)
-- 42

-- >>> runM errorAsIO (evalError err)
-- "Error dividing 1 by 0"
