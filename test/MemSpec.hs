module MemSpec where

import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Memory
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck


inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = do
  prop "remembers what you put in" $ \(a :: Word4) (b :: Word4) (addr :: Addr 4) ->
    evalCircuitT
        (memoryCell @4 @Word4 >>> unsafeReinterpret)
        (inputOverTime
          [ ((addr, Just W), a)
          , ((addr, Just R), b)
          ])
        1
      === Just a

