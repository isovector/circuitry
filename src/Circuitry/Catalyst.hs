{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RoleAnnotations #-}

{-# OPTIONS_GHC -Wall                               #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-do-bind                 #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Circuitry.Catalyst
  ( module Circuitry.Category
  , module Circuitry.Catalyst
  ) where

import           Circuitry.Category
import           Data.Bool (bool)
import           Data.Function (fix)
import           Data.Profunctor.Types
import           Data.Word (Word8)
import           Numeric.Natural (Natural)
import           Prelude hiding (id, (.), sum, zip)
import           Test.QuickCheck (CoArbitrary, Arbitrary (arbitrary), Function (function), functionMap, (===))
import           Test.QuickCheck.Arbitrary (CoArbitrary(coarbitrary))
import           Test.QuickCheck.Checkers


instance Arbitrary Natural where
  arbitrary = fmap (fromIntegral . abs @Integer) arbitrary

instance CoArbitrary Natural where
  coarbitrary = coarbitrary @Integer . fromIntegral

instance Function Natural where
  function = functionMap fromIntegral (fromIntegral @Integer . abs)


instance EqProp Word8 where
  (=-=) = (===)

newtype Signal a b = Signal
  { pumpSignal :: a -> (Signal a b, b)
  }
  deriving stock Functor

type role Signal representational representational

instance Applicative (Signal a) where
  pure b = Signal $ const $ (pure b, b)
  (<*>) (Signal sf) (Signal sb) = Signal $ \a ->
    let (sf', f) = sf a
        (sa', b) = sb a
     in (sf' <*> sa', f b)


instance (CoArbitrary a, Arbitrary b) => Arbitrary (Signal a b) where
  arbitrary = Signal <$> arbitrary

instance Profunctor Signal where
  dimap f g (Signal h) = Signal $ (dimap f g *** g) . h . f

instance Category Signal where
  type Ok Signal = TrivialConstraint
  id = Signal $ \a -> (id, a)
  Signal g . Signal f = Signal $ \a ->
    let (sf, b) = f a
        (sg, c) = g b
     in (sg . sf, c)
  {-# INLINE id #-}
  {-# INLINE (.) #-}


primSignal :: (a -> b) -> Signal a b
primSignal f = fix $ \me -> Signal $ \a -> (me, f a)
{-# INLINE primSignal #-}


instance Distrib Signal where
  distrib = primSignal distrib
  factor = primSignal factor

instance SymmetricProduct Signal where
  swap = primSignal swap
  reassoc = primSignal reassoc
  reassoc' = primSignal reassoc'

instance MonoidalProduct Signal where
  (***) (Signal f) (Signal g) = Signal $ \(al, ar) ->
    let (sf, bl) = f al
        (sg, br) = g ar
     in (sf *** sg, (bl, br))
  {-# INLINE (***) #-}

instance SymmetricSum Signal where
  swapE = primSignal swapE
  reassocE = primSignal reassocE

instance MonoidalSum Signal where
  (+++) sf sg = Signal $ \case
     Left  al -> (+++ sg) *** Left  $ pumpSignal sf al
     Right ar -> (sf +++) *** Right $ pumpSignal sg ar
  {-# INLINE (+++) #-}

instance Cartesian Signal where
  consume = primSignal consume
  copy = primSignal copy
  fst' = primSignal fst'
  snd' = primSignal snd'

instance Cocartesian Signal where
  injectL = primSignal injectL
  injectR = primSignal injectR
  unify = primSignal unify
  tag = primSignal tag


spike :: Time -> Time -> Bool
spike n t = bool False True $ n == t

type Time = Natural

