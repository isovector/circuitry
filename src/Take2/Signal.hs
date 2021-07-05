{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Take2.Signal where

import Circuitry.Category
import Clash.Sized.Vector (Vec)
import Data.Function (fix)
import Numeric.Natural (Natural)
import Prelude hiding (id, (.), sum, zip)
import Take2.Embed
import Test.QuickCheck (CoArbitrary(..), Arbitrary (..), Function (..), functionMap)


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


primSignal
    :: (Embed a, Embed b)
    => (Vec (SizeOf a) (Maybe Bool) -> Vec (SizeOf b) (Maybe Bool))
    -> Signal a b
primSignal f = fix $ \me -> Signal $ (me, ) . f
{-# INLINE primSignal #-}



type Time = Natural

instance Arbitrary Natural where
  arbitrary = fmap (fromIntegral . abs @Integer) arbitrary

instance CoArbitrary Natural where
  coarbitrary = coarbitrary @Integer . fromIntegral

instance Function Natural where
  function = functionMap fromIntegral (fromIntegral @Integer . abs)

