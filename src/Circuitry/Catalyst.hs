{-# LANGUAGE MagicHash       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Circuitry.Catalyst
  ( module Circuitry.Category
  , module Circuitry.Catalyst
  ) where

import           Circuitry.Category
import           Clash.Sized.Vector (Vec)
import qualified Clash.Sized.Vector as V
import           Data.Bool (bool)
import           Data.Function (fix)
import           Numeric.Natural (Natural)
import           Prelude hiding (id, (.), sum, zip)
import           Take2.Embed
import           Test.QuickCheck (CoArbitrary, Arbitrary (arbitrary), Function (function), functionMap)
import           Test.QuickCheck.Arbitrary (CoArbitrary(coarbitrary))


instance Arbitrary Natural where
  arbitrary = fmap (fromIntegral . abs @Integer) arbitrary

instance CoArbitrary Natural where
  coarbitrary = coarbitrary @Integer . fromIntegral

instance Function Natural where
  function = functionMap fromIntegral (fromIntegral @Integer . abs)


newtype Signal a b = Signal
  { pumpSignal :: Vec (SizeOf a) (Maybe Bool) -> (Signal a b, Vec (SizeOf b) (Maybe Bool))
  }


instance (CoArbitrary a, Arbitrary b, Embed b) => Arbitrary (Signal a b) where
  arbitrary = Signal <$> arbitrary

instance Category Signal where
  type Ok Signal = Embed
  id = Signal $ \a -> (id, a)
  Signal g . Signal f = Signal $ \a ->
    let (sf, b) = f a
        (sg, c) = g b
     in (sg . sf, c)
  {-# INLINE id #-}
  {-# INLINE (.) #-}


primSignal :: (Embed a, Embed b) => (a -> b) -> Signal a b
primSignal f = fix $ \me -> Signal $ \ma ->
  (me, ) $ case V.traverse# id ma of
    Just a  -> fmap Just $ embed $ f $ reify a
    Nothing -> V.repeat Nothing
{-# INLINE primSignal #-}


instance Distrib Signal where
  distrib = primSignal distrib
  factor = primSignal factor

instance SymmetricProduct Signal where
  swap = primSignal swap
  reassoc = primSignal reassoc
  reassoc' = primSignal reassoc'

instance MonoidalProduct Signal where
  (***) (Signal f) (Signal g) = Signal $ \v ->
    let (al, ar) = V.splitAtI v
        (sf, bl) = f al
        (sg, br) = g ar
     in (sf *** sg, bl V.++ br)
  {-# INLINE (***) #-}

instance SymmetricSum Signal where
  swapE = primSignal swapE
  reassocE = primSignal reassocE

instance MonoidalSum Signal where
  (+++)
      :: forall al bl ar br
       . Signal al bl
      -> Signal ar br
      -> Signal (Either al ar) (Either bl br)
  (+++) = undefined {- sf sg = Signal $ \v -> do
    let (tag, v') = V.splitAtI @1 v
    _
    case V.head tag of
      Nothing -> (sf +++ sg, V.repeat Nothing)
      Just False ->
        let (sf', l) = pumpSignal sf $ V.takeI v'
         in (sf' +++ sg, l V.++ V.repeat (Just False))
      Just True -> undefined-}
--      in case tag of
--      Left  al -> (+++ sg) *** Left  $ pumpSignal sf al
--      Right ar -> (sf +++) *** Right $ pumpSignal sg ar
--   {-# INLINE (+++) #-}

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

