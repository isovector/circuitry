module SimpleSpec where

import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Simple
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck
import Numeric.Natural (Natural)
import Data.Bits
import Data.Bool (bool)

instance Show (Circuit a b) where
  show _ = "cir"

spec :: Spec
spec = do
  prop "wtf" $ \b (c1 :: Circuit Word8 Word8) c2 a ->
    evalCircuit (ifC c1 c2) (b, a) 2
      === evalCircuit (bool c2 c1 b) a 2
