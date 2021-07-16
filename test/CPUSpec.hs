module CPUSpec where

import qualified Clash.Sized.Vector as V
import           Data.Bits
import           Data.Bool (bool)
import           Numeric.Natural (Natural)
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.CPU
import           Take2.Computer.Instruction
import           Take2.Computer.Poly
import           Take2.Computer.Register
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck


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
  evalCircuit (runProg prog) () (t * 3 - 1)


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

  -- prop "BranchZ positive" $ \r n b -> do
  --   let full_b = reify $ padV @8 @7 b
  --   fmap reg_PC (evalProgram
  --     [ ILoadLo r n   -- let a = 7
  --     , IBranchZ r full_b
  --     ] 2)
  --     === (Just $ fromIntegral $ bool 2 (2 + full_b) $ n == 0)

  prop "BranchZ negative" $ do
    let nop = INop $ V.repeat False
    fmap reg_PC (evalProgram
      [ IJump R1 10
      , nop
      , nop
      , nop
      , nop
      , nop
      , nop
      , nop
      , nop
      , nop
      , IBranchZ R1 $ twosComplement 6
      ] 2)
      === Just 5

  let b = 4
  prop "it multiplies!" $
    fmap reg_R11 (evalProgram
      [ ILoadLo R1 7    -- let a = 7
      , ILoadLo R2 0    --     i = 0
      , ILoadLo R3 b    --     b = `b`
      , ILoadLo R4 0    --     r = 0
      , IXOr R2 R3 R10  -- z = i ^ b
      , IBranchZ R10 3  -- if ( z != 0 ) // aka  i /= b {
      , IAddI R2 1 R2   --   i++
      , IAdd R1 R4 R4   --   r += a
      , IJump R16 4     -- }
      , IMove R4 R11
      ] (5 + (b + 1) * 2 + (b * 3)))
      === Just (b * 7)

twosComplement :: (Num a , Bits a) => a -> a
twosComplement = (+ 1) . complement

