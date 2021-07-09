module BusSpec where

import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Memory
import           Take2.Computer.Bus
import           Take2.Computer.ALU
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck
import qualified Data.Bits as B
import qualified Clash.Sized.Vector as V


inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = do
  prop "remembers what you put in" $
    forAllShrink arbitrary shrink $ \(a :: Word4) ->
    forAllShrink arbitrary shrink $ \(b :: Word4) ->
    forAllShrink arbitrary shrink $ \(addr :: Addr 4) ->
    forAllShrink arbitrary shrink $ \rom_addr ->
    forAllShrink arbitrary shrink $ \rom ->
    evalCircuitTT
        (bus @4 @Word4 rom >>> unsafeParse @Word4)
        (inputOverTime
          [ BusMemory $ MemoryCommand W addr a
          , BusAlu    $ AluAdd a b
          , BusMemory $ MemoryCommand R addr a
          , BusMemory $ MemoryCommand W addr b
          , BusAlu    $ AluNot a
          , BusAlu    $ AluOr a b
          , BusMemory $ MemoryCommand R addr 0
          , BusROM    $ rom_addr
          ])
        7
      === [ Nothing
          , Just (a + b)
          , Just a
          , Nothing
          , Just (B.complement a)
          , Just (a B..|. b)
          , Just b
          , Just $ rom V.!! (fromIntegral $ reify @Word4 (embed rom_addr))
          ]

