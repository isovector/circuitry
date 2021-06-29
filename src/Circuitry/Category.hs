{-# LANGUAGE CPP                     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE QuantifiedConstraints   #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE StarIsType              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module Circuitry.Category where

import qualified Control.Arrow as A
import           Data.Kind
import qualified Data.Profunctor as P
import           Data.Typeable
import           Data.Void
import qualified Prelude
import           Prelude hiding (id, (.))
import qualified Control.Arrow as C

class ( Ok k ()
      , forall x y okK. (Ok k x, Ok k y, okK ~ Ok k) => okK (x, y)
      , forall x y okK. (Ok k x, Ok k y, okK ~ Ok k) => okK (Either x y)
      ) => Category k where
  type Ok k :: Type -> Constraint
  id :: Ok k a => k a a
  (.) :: (AllOk k [a, b, c]) => k b c -> k a b -> k a c


class Category k => Recursive k where
  recurseL :: AllOk k [a, b, s] => (Either a s `k` Either b s) -> (a `k` b)
  recurseR :: AllOk k [a, b, s] => (Either s a `k` Either s b) -> (a `k` b)

type family AllOk k (t :: [Type]) :: Constraint where
  AllOk k '[] = ()
  AllOk k (t1 : ts) = (Ok k t1, AllOk k ts)

class TrivialConstraint a where
instance TrivialConstraint a where

instance Category (->) where
  type Ok (->) = TrivialConstraint
  id = Prelude.id
  (.) = (Prelude..)

instance Recursive (->) where
  recurseL = P.unleft
  recurseR = P.unright

class Category k => Fixed k where
  fixL :: AllOk k [a, b, s] => ((a, s) `k` (b, s)) -> (a `k` b)
  fixR :: AllOk k [a, b, s] => ((s, a) `k` (s, b)) -> (a `k` b)

instance Fixed (->) where
  fixL = P.unfirst
  fixR = P.unsecond

(<<<) :: (Category k, AllOk k [a, b, c]) => k b c -> k a b -> k a c
(<<<) = (.)
{-# INLINE (<<<) #-}

(>>>) :: (Category k, AllOk k [a, b, c]) => k a b -> k b c -> k a c
f >>> g = g . f
{-# INLINE (>>>) #-}


class SymmetricProduct k => MonoidalProduct k where
  {-# MINIMAL (***) | (first', second') #-}
  (***) :: AllOk k [al, bl, ar, br] => (al `k` bl) -> (ar `k` br) -> ((al, ar) `k` (bl, br))
  l *** r = first' l >>> second' r

  first' :: AllOk k [a, b, c] => (a `k` b) -> ((a, c) `k` (b, c))
  first' = flip (***) id

  second' :: AllOk k [a, b, c] => (a `k` b) -> ((c, a) `k` (c, b))
  second' = (***) id

instance MonoidalProduct (->) where
  (***) = (A.***)
  first' = A.first
  second' = A.second
  {-# INLINE (***) #-}
  {-# INLINE first' #-}
  {-# INLINE second' #-}

class SymmetricSum k => MonoidalSum k where
  {-# MINIMAL left | right #-}

  (+++) :: AllOk k [al, bl, ar, br] => (al `k` bl) -> (ar `k` br) -> ((Either al ar) `k` (Either bl br))
  l +++ r = left l >>> right r

  left :: AllOk k [a, b, c] => (a `k` b) -> ((Either a c) `k` (Either b c))
  left f = swapE >>> right f >>> swapE

  right :: AllOk k [a, b, c] => (a `k` b) -> ((Either c a) `k` (Either c b))
  right f = swapE >>> left f >>> swapE


class Category k => Distrib k where
  distrib :: AllOk k [a, b, c] => (a, Either b c) `k` (Either (a, b) (a, c))
  factor :: AllOk k [a, b, c] => (Either (a, b) (a, c)) `k` (a, Either b c)


instance MonoidalSum (->) where
  l +++ r = l A.+++ r
  left = A.left
  right = A.right

instance Distrib (->) where
  distrib (a, (Left b)) = Left (a, b)
  distrib (a, (Right c)) = Right (a, c)
  factor (Left (a, b)) = (a, Left b)
  factor (Right (a, c)) = (a, Right c)

class Category k => SymmetricProduct k where
  swap :: AllOk k [l, r] => (l, r) `k` (r, l)
  reassoc :: AllOk k [a, b, c] => (a, (b, c)) `k` ((a, b), c)

{-# RULES
"swap . swap" forall a. swap (swap a) = a
#-}

class Category k => SymmetricSum k where
  swapE :: AllOk k [l, r] => (Either l r) `k` (Either r l)
  reassocE :: AllOk k [a, b, c]
           => (Either a (Either b c)) `k` Either (Either a b) c

instance SymmetricProduct (->) where
  swap (a, b) = (b, a)
  reassoc (a, (b, c)) = ((a, b), c)
  {-# INLINE swap #-}
  {-# INLINE reassoc #-}

instance SymmetricSum (->) where
  swapE (Left a) = Right a
  swapE (Right a) = Left a
  reassocE (Left a) = Left (Left a)
  reassocE (Right (Left b)) = Left (Right b)
  reassocE (Right (Right c)) = Right c

class CategoryPlus k => CategoryZero k where
  zeroC :: AllOk k [a, b] => k a b

class Category k => CategoryPlus k where
  (<+>) :: AllOk k [a, b] => k a b -> k a b -> k a b


class MonoidalProduct k => Cartesian k where
  (&&&) :: AllOk k [a, l, r]
        => (a `k` l) -> (a `k` r) -> (a `k` (l, r))
  l &&& r = copy >>> (l *** r)

  consume :: Ok k a => a `k` ()
  copy :: Ok k a => a `k` (a, a)
  fst' :: AllOk k [l, r] => (l, r) `k` l
  snd' :: AllOk k [l, r] => (l, r) `k` r

instance Cartesian (->) where
  copy x = (x, x)
  consume _ = ()
  fst' = fst
  snd' = snd

class MonoidalSum k => Cocartesian k where
  (|||) :: AllOk k [al, ar, b] => (al `k` b) -> (ar `k` b) -> (Either al ar `k` b)
  (|||) l r = (l +++ r) >>> unify

  injectL :: AllOk k [a, b] => a `k` (Either a b)
  injectR :: AllOk k [a, b] => a `k` (Either b a)

  unify :: Ok k a => Either a a `k` a
  -- | tags 'Right' when 'True', 'Left' when 'False'
  tag :: AllOk k [Bool, a] => k (Bool, a) (Either a a)

instance Cocartesian (->) where
  injectL = Left
  injectR = Right
  unify = either id id
  tag (True, a) = Right a
  tag (False, a) = Left a


infixr 1 >>>
infixr 1 <<<

