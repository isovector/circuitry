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
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

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

(>>>) :: (Category k, AllOk k [a, b, c]) => k a b -> k b c -> k a c
f >>> g = g . f


class SymmetricProduct k => MonoidalProduct k where
  {-# MINIMAL first' | second' #-}
  (***) :: AllOk k [al, bl, ar, br] => (al `k` bl) -> (ar `k` br) -> ((al, ar) `k` (bl, br))
  l *** r = first' l >>> second' r

  first' :: AllOk k [a, b, c] => (a `k` b) -> ((a, c) `k` (b, c))
  first' f = swap >>> second' f >>> swap

  second' :: AllOk k [a, b, c] => (a `k` b) -> ((c, a) `k` (c, b))
  second' f = swap >>> first' f >>> swap

instance MonoidalProduct (->) where
  (***) = (A.***)
  first' = A.first
  second' = A.second

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

class Category k => SymmetricSum k where
  swapE :: AllOk k [l, r] => (Either l r) `k` (Either r l)
  reassocE :: AllOk k [a, b, c]
           => (Either a (Either b c)) `k` Either (Either a b) c

instance SymmetricProduct (->) where
  swap (a, b) = (b, a)
  reassoc (a, (b, c)) = ((a, b), c)

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




data Catalyst (ct :: Type -> Constraint) (p :: * -> * -> *) a b where
  ID :: ct x => Catalyst ct p x x
  Comp :: Catalyst ct p x y -> Catalyst ct p y z -> Catalyst ct p x z

  Swap :: (ct a, ct b) => Catalyst ct p (a, b) (b, a)
  Reassoc :: (ct a, ct b, ct c) => Catalyst ct p (a, (b, c)) ((a, b), c)

  SwapE :: (ct a, ct b) => Catalyst ct p (Either a b) (Either b a)
  ReassocE :: (ct a, ct b, ct c) => Catalyst ct p (Either a (Either b c)) (Either (Either a b) c)

  First :: (ct a, ct b, ct m) => Catalyst ct p a b -> Catalyst ct p (a, m) (b, m)
  Second :: (ct a, ct b, ct m) => Catalyst ct p a b -> Catalyst ct p (m, a) (m, b)
  -- (***)
  Alongside :: (ct a, ct a', ct b, ct b') => Catalyst ct p a b -> Catalyst ct p a' b' -> Catalyst ct p (a, a') (b, b')
  -- (&&&)
  Fanout :: (ct a, ct b, ct b') => Catalyst ct p a b -> Catalyst ct p a b' -> Catalyst ct p a (b, b')

  Left' :: (ct a, ct x, ct b) => Catalyst ct p a b -> Catalyst ct p (Either a x) (Either b x)
  Right' :: (ct a, ct b, ct x) => Catalyst ct p a b -> Catalyst ct p (Either x a) (Either x b)
  -- (+++)
  EitherOf :: (ct a, ct b, ct a', ct b') => Catalyst ct p a b -> Catalyst ct p a' b' -> Catalyst ct p (Either a a') (Either b b')
  -- (|||)
  Fanin :: (ct a, ct b, ct a') => Catalyst ct p a b -> Catalyst ct p a' b -> Catalyst ct p (Either a a') b

  Copy :: (ct x) => Catalyst ct p x (x, x)
  Consume :: (ct x) => Catalyst ct p x ()
  Fst :: (ct a, ct b) => Catalyst ct p (a, b) a
  Snd :: (ct a, ct b) => Catalyst ct p (a, b) b

  InjectL :: (ct a, ct b) => Catalyst ct p a (Either a b)
  InjectR :: (ct a, ct b) => Catalyst ct p b (Either a b)
  Unify :: (ct a) => Catalyst ct p (Either a a) a
  Tag :: (ct a, ct Bool) => Catalyst ct p (Bool, a) (Either a a)

  RecurseL :: (ct a, ct b, ct d) => Catalyst ct p (Either a d) (Either b d) -> Catalyst ct p a b
  RecurseR :: (ct a, ct b, ct d) => Catalyst ct p (Either d a) (Either d b) -> Catalyst ct p a b

  Distribute :: (ct a, ct b, ct c) => Catalyst ct p (a, Either b c) (Either (a, b) (a, c))
  Factor :: (ct a, ct b, ct c) => Catalyst ct p (Either (a, b) (a, c)) (a, Either b c)

  FixL :: (ct a, ct b, ct d) => Catalyst ct p (a, d) (b, d) -> Catalyst ct p a b
  FixR :: (ct a, ct b, ct d) => Catalyst ct p (d, a) (d, b) -> Catalyst ct p a b

  LiftC :: (ct a, ct b) => p a b -> Catalyst ct p a b



instance (forall x y. Show (c x y)) => Show (Catalyst r c a b) where
  show
    = \case
        Fst -> "fst"
        Snd -> "snd"
        Copy -> "copy"
        Consume -> "consume"
        Swap -> "swap"
        Reassoc -> "reassoc"
        SwapE -> "swapE"
        ReassocE -> "reassocE"

        InjectL -> "injectL"
        InjectR -> "injectR"
        Unify -> "unify"
        Tag -> "tag"
        (First l) -> "(first' " <> show l <> ")"
        (Second l) -> "(second' " <> show l <> ")"
        (Alongside l r) -> "(" <> show l <> " *** " <> show r <>  ")"
        (Fanout l r) -> "(" <> show l <> " &&& " <> show r  <> ")"
        (Left' l) -> "(left " <> show l <> ")"
        (Right' r) -> "(right " <> show r <> ")"
        (EitherOf l r) -> "(" <> show l <> " +++ " <> show r <> ")"
        (Fanin l r) -> "(" <> show l <> " +++ " <> show r <> ")"
        (LiftC cab) -> show cab
        ID -> "id"
        (Comp l r) -> "(" <> show l <> " >>> " <> show r <> ")"
        (RecurseL l) -> "(recurseR " <> show l <> ")"
        (RecurseR r) -> "(recurseL " <> show r <> ")"
        (FixL l) -> "(fixL " <> show l <> ")"
        (FixR r) -> "(fixR " <> show r <> ")"
        (Distribute) -> "distrib"
        (Factor) -> "factor"


#define CONSTRAINTS(r) ( r () \
                      , r Void \
                      , forall x y. (r x, r y) => r (x, y) \
                      , forall x y. (r x, r y) => r (Either x y) \
                       )

instance CONSTRAINTS(r) => Category (Catalyst r c) where
  type Ok (Catalyst r c) = r
  id = ID
  (.) = flip Comp

instance CONSTRAINTS(r) => Cartesian (Catalyst r c) where
  copy = Copy
  consume = Consume
  fst' = Fst
  snd' = Snd

instance CONSTRAINTS(r) => Cocartesian (Catalyst r c) where
  injectL = InjectL
  injectR = InjectR
  unify = Unify
  tag = Tag

instance CONSTRAINTS(r) => SymmetricProduct (Catalyst r c) where
  swap = Swap
  reassoc = Reassoc

instance CONSTRAINTS(r) => SymmetricSum (Catalyst r c) where
  swapE = SwapE
  reassocE = ReassocE

instance CONSTRAINTS(r) => MonoidalProduct (Catalyst r c) where
  (***) = Alongside
  first' = First
  second' = Second

instance CONSTRAINTS(r) => MonoidalSum (Catalyst r c) where
  (+++) = EitherOf
  left = Left'
  right = Right'

instance CONSTRAINTS(r) => Recursive (Catalyst r c) where
  recurseL = RecurseL
  recurseR = RecurseR

instance CONSTRAINTS(r) => Fixed (Catalyst r c) where
  fixL = FixL
  fixR = FixR

instance CONSTRAINTS(r) => Distrib (Catalyst r c) where
  distrib = Distribute
  factor = Factor



runFree
    :: forall r p c a b
     . (Category p, Fixed p, Cartesian p, Cocartesian p, Recursive p, Distrib p, Ok p ~ TrivialConstraint)
    => (forall x y. AllOk p [x, y] => c x y -> p x y)
    -> Catalyst r c a b
    -> p a b
runFree interp = \case
  LiftC c -> interp c
  Fst -> fst'
  Snd -> snd'
  Copy -> copy
  Consume -> consume
  Swap -> swap
  SwapE -> swapE
  Reassoc -> reassoc
  ReassocE -> reassocE
  InjectL -> injectL
  InjectR -> injectR
  Unify -> unify
  Tag -> tag
  First p -> first' (runFree interp p)
  Second p -> second' (runFree interp p)
  Alongside l r -> runFree interp l *** runFree interp r
  Fanout l r -> runFree interp l &&& runFree interp r
  Left' p -> left (runFree interp p)
  Right' p -> right (runFree interp p)
  Fanin l r -> runFree interp l ||| runFree interp r
  EitherOf l r -> runFree interp l +++ runFree interp r
  Comp l r -> runFree interp l >>> runFree interp r
  ID -> id
  RecurseL l -> recurseL (runFree interp l)
  RecurseR r -> recurseR (runFree interp r)
  FixL l -> fixL (runFree interp l)
  FixR r -> fixR (runFree interp r)
  Distribute -> distrib
  Factor -> factor

liftC :: (r a, r b) => c a b -> Catalyst r c a b
liftC = LiftC

infixr 1 >>>
infixr 1 <<<

