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
  prop "get . put = pure" $ \(a :: Word2) (b :: Word2) (addr :: Addr 2) ->
    evalCircuitT
        (memoryCell @2 @Word2 >>> unsafeReinterpret)
        (inputOverTime
          [ MemoryCommand W addr a
          , MemoryCommand R addr b
          ])
        1
      === Just a

  prop "put . put = put" $ \(a :: Word2) (b :: Word2) (addr :: Addr 2) ->
    evalCircuitT
        (memoryCell @2 @Word2 >>> unsafeReinterpret)
        (inputOverTime
          [ MemoryCommand W addr a
          , MemoryCommand W addr b
          , MemoryCommand R addr 0
          ])
        2
      === Just b

  prop "high Z doesn't corrupt memory" $ \(a :: Word2) (addr :: Addr 1) arb ->
    evalCircuitT
        (first' serial >>> tribufAll >>> unsafeParse >>> memoryCell @1 @Word2 >>> unsafeReinterpret)
        (inputOverTime
          [ (MemoryCommand W addr a, True)
          , (arb, False)
          , (MemoryCommand R addr a, True)
          ])
        2
      === Just a

