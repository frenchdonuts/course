{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RebindableSyntax #-}

module Course.State where

import Course.Core
import qualified Prelude as P
import Course.Optional
import Course.List
import Course.Functor
import Course.Apply
import Course.Applicative
import Course.Bind
import Course.Monad
import qualified Data.Set as S

-- $setup
-- >>> import Test.QuickCheck.Function
-- >>> import Data.List(nub)
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(fmap)
-- >>> import Course.Core
-- >>> import Course.List
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap listh arbitrary

-- A `State` is a function from a state value `s` to (a produced value `a`, and a resulting state `s`).
newtype State s a =
  State {
    runState ::
      s
      -> (a, s)
  }

-- | Implement the `Functor` instance for `State s`.
-- >>> runState ((+1) <$> pure 0) 0
-- (1,0)
instance Functor (State s) where
  (<$>) ::
    (a -> b)
    -> State s a
    -> State s b
  (<$>) f (State k) = State (\s -> newPair $ k s)
    where newPair (a, s') = (f a, s')
-- (a -> b) -> (s -> (a, s)) -> (s -> (b, s))

-- | Implement the `Apply` instance for `State s`.
-- >>> runState (pure (+1) <*> pure 0) 0
-- (1,0)
--
-- >>> import qualified Prelude as P
-- >>> runState (State (\s -> ((+3), s P.++ ["apple"])) <*> State (\s -> (7, s P.++ ["banana"]))) []
-- (10,["apple","banana"])
instance Apply (State s) where
  (<*>) ::
    State s (a -> b)
    -> State s a
    -> State s b
  (<*>) (State fs) (State as) =
    State (\s -> let (f, s1) = fs s
                     (a, s2) = as s1
                  in (f a, s2))


-- | Implement the `Applicative` instance for `State s`.
-- >>> runState (pure 2) 0
-- (2,0)
instance Applicative (State s) where
  pure ::
    a
    -> State s a
  pure a = State (\s' -> (a, s'))

-- | Implement the `Bind` instance for `State s`.
-- >>> runState ((const $ put 2) =<< put 1) 0
-- ((),2)
instance Bind (State s) where
  (=<<) ::
    (a -> State s b)
    -> State s a
    -> State s b
  (=<<) f (State as) =
    State (\s -> let (a, s1) = as s
                  in runState (f a) s1)
-- f =<< s

instance Monad (State s) where

-- | Run the `State` seeded with `s` and retrieve the resulting state.
--
-- prop> \(Fun _ f) -> exec (State f) s == snd (runState (State f) s)
exec ::
  State s a
  -> s
  -> s
exec stateM s = snd $ runState stateM s

-- | Run the `State` seeded with `s` and retrieve the resulting value.
--
-- prop> \(Fun _ f) -> eval (State f) s == fst (runState (State f) s)
eval ::
  State s a
  -> s
  -> a
eval stateM s = fst $ runState stateM s

-- | A `State` where the state also distributes into the produced value.
--
-- >>> runState get 0
-- (0,0)
get ::
  State s s
get = State (\s -> (s,s))

-- | A `State` where the resulting state is seeded with the given value.
--
-- >>> runState (put 1) 0
-- ((),1)
put ::
  s
  -> State s ()
put s0 = State (\s -> ((),s0))
-- Also: State . const . (,) ()

-- | Find the first element in a `List` that satisfies a given predicate.
-- It is possible that no element is found, hence an `Optional` result.
-- However, while performing the search, we sequence some `Monad` effect through.
--
-- Note the similarity of the type signature to List#find
-- where the effect appears in every return position:
--   find ::  (a ->   Bool) -> List a ->    Optional a
--   findM :: (a -> f Bool) -> List a -> f (Optional a)
--
-- >>> let p x = (\s -> (const $ pure (x == 'c')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Full 'c',3)
--
-- >>> let p x = (\s -> (const $ pure (x == 'i')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Empty,8)
findM ::
  Monad f =>
  (a -> f Bool)
  -> List a
  -> f (Optional a)
findM p = foldRight stepFn (pure Empty)
  where stepFn x acc = (p x) >>= (\b -> if b then (pure $ Full x) else acc)
-- (a -> f Bool) -> List a -> f (Optional a)
-- Using findM below for firstRepeat and distinct made me realize what Erik Meijer said about Monads
-- Monads let you focus on the happy path!
--  (a -> m Bool):
--    m - all this other "stuff"(IO, State, whatever) is going on BUT
--    all you have to focus on is the Bool value I return!!

-- | Find the first element in a `List` that repeats.
-- It is possible that no element repeats, hence an `Optional` result.
--
-- /Tip:/ Use `findM` and `State` with a @Data.Set#Set@.
--
-- prop> case firstRepeat xs of Empty -> let xs' = hlist xs in nub xs' == xs'; Full x -> length (filter (== x) xs) > 1
-- prop> case firstRepeat xs of Empty -> True; Full x -> let (l, (rx :. rs)) = span (/= x) xs in let (l2, r2) = span (/= x) rs in let l3 = hlist (l ++ (rx :. Nil) ++ l2) in nub l3 == l3
firstRepeat ::
  Ord a =>
  List a
  -> Optional a
firstRepeat xs = eval (findM p xs) S.empty
  where p x = State (\set -> (S.member x set, S.insert x set))
-- findM :: (a -> f Bool) -> List a -> f Optional a
-- p :: Ord a => a -> State (S.Set a) Bool
-- State: a set representing the elements we have seen
-- Value: True if we have seen this value before, False if not
--  This is the only thing findM has to worry about

-- | Remove all duplicate elements in a `List`.
-- /Tip:/ Use `filtering` and `State` with a @Data.Set#Set@.
--
-- prop> firstRepeat (distinct xs) == Empty
--
-- prop> distinct xs == distinct (flatMap (\x -> x :. x :. Nil) xs)
distinct ::
  Ord a =>
  List a
  -> List a
distinct xs = eval (filtering p xs) S.empty
  where p x = State (\set -> (not $ S.member x set, S.insert x set))
-- filtering :: ...=> (a -> f Bool) -> List a -> f (List a)
-- f Bool ==> State Set Bool
-- p :: a -> State Set Bool
-- We want to return True (include this element) if we have NOT seen it before
-- State (Set) represents elements we have seen

-- | A happy number is a positive integer, where the sum of the square of its digits eventually reaches 1 after repetition.
-- In contrast, a sad number (not a happy number) is where the sum of the square of its digits never reaches 1
-- because it results in a recurring sequence.
--
-- /Tip:/ Use `findM` with `State` and `produce`.
--  findM :: (a -> f Bool) -> List a -> f Optional a
--  produce :: (a -> a) -> a -> List a (great for defining recurrence relations)
--
-- /Tip:/ Use `join` to write a @square@ function.
--  join :: f (f a) -> f a
--
-- /Tip:/ Use library functions: @Optional#contains@, @Data.Char#digitToInt@.
--  Course.Optional.contains :: a -> Optional a -> Bool
--  Data.Char.digitToInt :: Char -> Int
--
-- >>> isHappy 4
-- False
--
-- >>> isHappy 7
-- True
--
-- >>> isHappy 42
-- False
--
-- >>> isHappy 44
-- True
isHappy ::
  Integer
  -> Bool
isHappy x = Course.Optional.contains 1 (firstRepeat $ happySequence x)

happySequence seed = sum(squareOfDigits seed) :. happySequence (sum(squareOfDigits seed))
-- happySequence can also be written as:
-- produce (toInteger . sum . map (join (*) . digitToInt) . show')
-- How does join (*) turn into square? Let's look at the types
-- join :: f (f a) -> f a
--   f ==> (->) a
-- join :: Num a => (->) a ((->) a a) -> (-> a) a
-- join :: Num a => a -> (a -> a) -> (a -> a)
-- join (*) =
--   id =<< (*)          <Definition: f =<< g = (\t -> f (g t) t)>
--   (\t -> id ((*) t) t)
--   (\t -> ((*) t) t)
--   (\t -> (*) t t)
--   (\t -> t * t)
-- square
-- Here we learn about how join works for any binary function f:
--  join f = (\x -> f x x)

squareOfDigits :: Integer -> List Integer
squareOfDigits i = map square (digits i)

digits :: Integral a => a -> List a
digits i
  | (i < 10) = i :. Nil
  | otherwise = (i `mod` 10) :. digits (i `div` 10)

square :: Num a => a -> a
square x = x * x
-- Return True if sum of square of digits eventually is 1
-- Return False if we see a number we already saw (whose sum of square of digits is not 1)
-- 7 -> 49
-- 4^2 + 9^2 = 97
-- 9^2 + 7^2 = 130
-- 1^2 + 3^2 + 0 = 10
-- 1^2 + 0 = 1 -> True
