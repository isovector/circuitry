module CPUSpec where

import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.CPU
import           Take2.Computer.Instruction
import           Take2.Computer.Register
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck
import Numeric.Natural (Natural)
import Data.Bits


runProg :: [Instruction] -> Circuit () (Registers PC SP W)
runProg prog
    = cpu
    . fmap (reify . embed)
    . V.unsafeFromList
    . mappend prog
    . repeat
    . INop
    $ V.repeat False


evalProgram :: [Instruction] -> Natural -> Maybe (Registers PC SP W)
evalProgram prog t =
  evalCircuit (runProg prog >>> traceC "final") () (t * 3 - 1)


spec :: Spec
spec = do
  -- prop "it computes!" $
  --   fmap reg_R16 (evalProgram
  --     [ ILoadLo R1 1
  --     , ILoadLo R2 2
  --     , ILoadLo R3 3
  --     , ILoadLo R4 4
  --     , ILoadHi R5 1
  --     , ILoadLo R5 5
  --     , IAdd R16 R1 R16
  --     , IAdd R16 R2 R16
  --     , IAdd R16 R3 R16
  --     , IAdd R16 R4 R16
  --     , IAdd R16 R5 R16
  --     ] 11)
  --     === Just 271

  -- prop "it loops!" $
  --   fmap reg_R1 (evalProgram
  --     [ ILoadLo R1 255
  --     , ILoadLo R2 2
  --     , ILoadLo R3 1
  --     , IAdd R1 R3 R1
  --     , IJump R2 1
  --     ] 8)
  --     === Just 258

  let b = 4
  prop "it multiplies!" $
    fmap reg_R11 (evalProgram
      [ ILoadLo R1 7   -- let a = 7
      , ILoadLo R2 0   --     i = 0
      , ILoadLo R3 0   --     b = 4
      , ILoadLo R4 0   --     r = 0
      , ILoadLo R5 1   --     j = 1
      , IXOr R2 R3 R10  -- z = i ^ b
      , IBranchZ R10 3
      , IAdd R2 R5 R2  -- i++
      , IAdd R1 R4 R4  -- r += a
      , IJump R16 5
      , IMove R4 R11
      ] 7)
      === Just (b * 7)

twosComplement :: (Num a , Bits a) => a -> a
twosComplement = (+ 1) . complement

