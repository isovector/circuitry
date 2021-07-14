module RegisterSpec where

import qualified Clash.Sized.Vector as V
import           Control.Lens ((.~))
import           Data.Monoid
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Register
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck


inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = pure ()
