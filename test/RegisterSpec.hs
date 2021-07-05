module RegisterSpec where

import Control.Lens ((.~))
import Data.Monoid
import Prelude hiding ((.), id, sum)
import Take2.Computer.Register
import Take2.Machinery
import Test.Hspec
import Test.Hspec.QuickCheck


inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = do
  -- prop "registers work" $ \(val1 :: (Register, Word4)) (take 8 -> vals :: [(Register, Word4)]) ->
  --   evalCircuitT
  --     (registerStore @Word4)
  --     (inputOverTime (val1 : vals))
  --     (fromIntegral (length vals))
  --       === Just (foldRegisters (val1 : vals) $ Registers 0 0 0)

  prop "cpu spec" $
    evalCircuitT
      (cpu @Word4)
      (inputOverTime
        [ (JMP, (5, 0))
        , (MOV, (fromIntegral $ fromEnum OP2, 13))
        , (INC, (0, 0))
        , (INC, (0, 0))
        ])
      3
        === Just (Registers { reg_PC =  5, reg_OP1 = 2, reg_OP2 = 13 })


foldRegisters :: forall a. Num a => [(Register, a)] -> Registers a -> Registers a
foldRegisters = fmap (appEndo . getDual) $ foldMap $ \(reg, a) ->
  Dual $ Endo $ case reg of
    NO_REGISTER -> id
    PC          -> #reg_PC .~ a
    OP1         -> #reg_OP1 .~ a
    OP2         -> #reg_OP2 .~ a


