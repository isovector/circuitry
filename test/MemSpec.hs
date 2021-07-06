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
  prop "get . put = pure" $ \(a :: Word4) (b :: Word4) (addr :: Addr 4) ->
    evalCircuitT
        (memoryCell @4 @Word4 >>> unsafeReinterpret)
        (inputOverTime
          [ MemoryCommand (Just W) addr a
          , MemoryCommand (Just R) addr b
          ])
        1
      === Just a

  prop "put . put = put" $ \(a :: Word4) (b :: Word4) (addr :: Addr 4) ->
    evalCircuitT
        (memoryCell @4 @Word4 >>> unsafeReinterpret)
        (inputOverTime
          [ MemoryCommand (Just W) addr a
          , MemoryCommand (Just W) addr b
          , MemoryCommand (Just R) addr 0
          ])
        2
      === Just b

