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
spec = do
  prop "get . set" $ \(v :: Word4) (r :: Register) (rs :: Registers Word4 Word4 Word4) ->
    evalCircuit
      (first' setReg >>> getReg)
      (((r, v), rs), r)
      2
      === Just v

  prop "set . get" $ \(v :: Word4) (r :: Register) (rs :: Registers Word4 Word4 Word4) ->
    evalCircuit
      (first' (second' getReg) >>> setReg)
      ((r, (rs, r)), rs)
      2
      === Just rs

