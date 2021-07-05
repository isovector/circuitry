module RegisterSpec where

import qualified Clash.Sized.Vector as V
import           Control.Lens ((.~))
import           Data.Monoid
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Register
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck


inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = do
  prop "registers work" $ \(val1 :: (Register, Word4)) (take 8 -> vals :: [(Register, Word4)]) ->
    evalCircuitT
      (second' serial >>> registerStore @Word4 @Word4 @Word4)
      (inputOverTime (val1 : vals))
      (fromIntegral (length vals))
        === Just (foldRegisters (val1 : vals) $ Registers 0 0 0 0 0 $ Flags False False False False)

--   prop "cpu spec" $
--     evalCircuitT
--       (cpu @Word4)
--       (inputOverTime
--         [ (JMP, (5, 0))
--         , (MOV, (fromIntegral $ fromEnum OP2, 13))
--         , (INC, (0, 0))
--         , (INC, (0, 0))
--         ])
--       3
--         === Just (Registers { reg_PC =  5, reg_OP1 = 2, reg_OP2 = 13 })


foldRegisters
    :: forall pc sp word
     . (Num pc, SizeOf sp <= SizeOf pc, SizeOf word <= SizeOf pc, SizeOf Flags <= SizeOf pc, Embed pc, Embed sp, Embed word)
    => [(Register, pc)]
    -> Registers pc sp word
    -> Registers pc sp word
foldRegisters = fmap (appEndo . getDual) $ foldMap $ \(reg, a) ->
  Dual $ Endo $ case reg of
    NO_REGISTER -> id
    PC          -> #reg_PC    .~ a
    SP          -> #reg_SP    .~ reify (V.takeI @_ @(SizeOf pc - SizeOf sp) $ embed a)
    X           -> #reg_X     .~ reify (V.takeI @_ @(SizeOf pc - SizeOf word) $ embed a)
    Y           -> #reg_Y     .~ reify (V.takeI @_ @(SizeOf pc - SizeOf word) $ embed a)
    A           -> #reg_A     .~ reify (V.takeI @_ @(SizeOf pc - SizeOf word) $ embed a)
    FLAGS       -> #reg_flags .~ reify (V.takeI @_ @(SizeOf pc - SizeOf Flags) $ embed a)

