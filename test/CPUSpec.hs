module CPUSpec where

import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.CPU
import           Take2.Computer.Instruction
import           Take2.Computer.Register
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck


prog :: [Instruction]
prog =
  [ ILoadLo R1 1
  , ILoadLo R2 2
  , ILoadLo R3 3
  , ILoadLo R4 4
  , ILoadHi R5 1
  , ILoadLo R5 5
  , IAdd R16 R1 R16
  , IAdd R16 R2 R16
  , IAdd R16 R3 R16
  , IAdd R16 R4 R16
  , IAdd R16 R5 R16
  ]


runProg :: Circuit () (Registers PC SP W)
runProg
    = cpu
    . fmap (reify . embed)
    . V.unsafeFromList
    . mappend prog
    . repeat
    . PADDING_
    $ V.repeat False


spec :: Spec
spec = do
  prop "it computes!" $
    evalCircuit
        (runProg >>> proj #reg_R16)
        ()
        (fromIntegral (length prog ) * 3 - 1)
      === Just 271

