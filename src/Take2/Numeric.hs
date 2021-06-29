
module Take2.Numeric where

import           Circuitry.Category (first')
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import qualified Data.Bits as B
import           Data.Word
import           Take2.Embed

class Numeric a where
  zero :: a
  default zero :: Num a => a
  zero = 0

  one :: a
  default one :: Num a => a
  one = 1

  addNumeric :: a -> a -> (a, Bool)
  default addNumeric :: (Num a, Ord a, Bounded a) => a -> a -> (a, Bool)
  addNumeric a b = (a + b, maxBound - a <= b)

instance Numeric Bool where
  zero = False
  one = True
  addNumeric a b = (B.xor a b, a && b)

instance Numeric Word8
instance Numeric Word16
instance Numeric Word32
instance Numeric Word64

instance Numeric (Vec 8 Bool) where
  zero = V.repeat False
  one = V.repeat False V.++ Cons True Nil
  addNumeric v1 v2 =
    first' embed $ reify @Word8 v1 `addNumeric` reify v2

