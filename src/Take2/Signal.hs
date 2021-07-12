{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Take2.Signal where

import           Circuitry.Category
import           Clash.Sized.Vector (Vec)
import qualified Clash.Sized.Vector as V
import           Control.Monad.ST (ST)
import           Numeric.Natural (Natural)
import           Prelude hiding (id, (.), sum, zip)
import           Take2.Embed
import           Test.QuickCheck (CoArbitrary(..), Arbitrary (..), Function (..), functionMap)
import           Unsafe.Coerce (unsafeCoerce)


newtype Signal s a b = Signal
  { pumpSignal
      :: forall s'
       . Vec (SizeOf a) (Maybe Bool)
      -> ST s (Signal s' a b, Vec (SizeOf b) (Maybe Bool))
  }


data SomeSignal a b where
  SomeSignal :: Signal s a b -> SomeSignal a b


unsafeCoerceSignalToken :: Signal s a b -> Signal s' a b
unsafeCoerceSignalToken = unsafeCoerce


instance (CoArbitrary a, Arbitrary b, Embed b) => Arbitrary (Signal s a b) where
  arbitrary = do
    (f :: Vec (SizeOf a) (Maybe Bool) -> (Signal s a b, Vec (SizeOf b) (Maybe Bool)))
      <- arbitrary
    pure $ Signal $ pure . first' unsafeCoerce . f


instance Category (Signal s) where
  type Ok (Signal s) = Embed
  id = Signal $ \a -> pure (id, a)
  Signal g . Signal f = Signal $ \a -> do
    (sf, b) <- f a
    (sg, c) <- g b
    pure (sg . sf, c)
  {-# INLINE id #-}
  {-# INLINE (.) #-}


primSignal
    :: (Embed a, Embed b)
    => (Vec (SizeOf a) (Maybe Bool) -> Vec (SizeOf b) (Maybe Bool))
    -> Signal s a b
primSignal f = Signal $ pure . (primSignal f, ) . f
{-# INLINE primSignal #-}


vacuousSignal :: (Embed b, Embed a) => Signal s a b
vacuousSignal = primSignal $ const $ V.repeat Nothing



type Time = Natural

instance Arbitrary Natural where
  arbitrary = fmap (fromIntegral . abs @Integer) arbitrary

instance CoArbitrary Natural where
  coarbitrary = coarbitrary @Integer . fromIntegral

instance Function Natural where
  function = functionMap fromIntegral (fromIntegral @Integer . abs)

