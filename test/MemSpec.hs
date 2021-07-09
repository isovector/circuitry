module MemSpec where

import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Addressed (decode)
import           Take2.Computer.Memory
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck


inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = do
  prop "decode indexes in order" $ \(addr :: Addr 4) t ->
    evalCircuit
        (decode)
        addr
        t
      === Just ( V.unsafeFromList @16
               $ fmap (== (fromIntegral $ reify @Word4 $ embed addr))
               $ [minBound @Word4 .. maxBound]
               )

  prop "rom read" $ \(addr :: Addr 4) (rom :: Vec 16 Word4) t ->
    evalCircuit
        (mkRom rom)
        addr
        t
      === Just (rom V.!! reify @Word4 (embed addr))

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

