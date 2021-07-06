module MemSpec where

import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Memory
import           Take2.Computer.Bus
import           Take2.Computer.ALU
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck
import qualified Data.Bits as B


inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = do
  prop "remembers what you put in" $ \(a :: Word4) (b :: Word4) (addr :: Addr 4) ->
    evalCircuitTT
        (bus @4 @Word4 >>> unsafeParse @Word4)
        (inputOverTime
          [ (MemoryBus, Left $ MemoryCommand (Identity W) addr a)
          , (AluBus, Right $ AluCommand AluOpAdd a b)
          , (MemoryBus, Left $ MemoryCommand (Identity R) addr a)
          , (MemoryBus, Left $ MemoryCommand (Identity W) addr b)
          , (AluBus, Right $ AluCommand AluOpNot a b)
          , (AluBus, Right $ AluCommand AluOpOr a b)
          , (MemoryBus, Left $ MemoryCommand (Identity R) addr 0)
          ])
        6
      === [ Nothing
          , Just (a + b)
          , Just a
          , Nothing
          , Just (B.complement a)
          , Just (a B..|. b)
          , Just b
          ]


