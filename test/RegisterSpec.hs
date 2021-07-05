module RegisterSpec where

import Control.Lens ((.~))
import Data.Monoid
import Prelude hiding ((.), id, sum)
import Take2.Computer.Register
import Take2.Machinery
import Test.Hspec
import Test.Hspec.QuickCheck
import Data.Generics.Product



inputOverTime :: [a] -> Time -> a
inputOverTime  as t = as !! fromIntegral t


spec :: Spec
spec = do
  prop "registers work" $ \(val1 :: (Register, Word4)) (take 8 -> vals :: [(Register, Word4)]) ->
    evalCircuitT
      (registerStore @Word4)
      (inputOverTime (val1 : vals))
      (fromIntegral (length vals))
        === Just (foldRegisters (reverse (val1 : vals)) $ Registers 0 0 0)


foldRegisters :: forall a. Num a => [(Register, a)] -> Registers a -> Registers a
foldRegisters = fmap appEndo $ foldMap $ \(reg, a) ->
  Endo $ case reg of
    NO_REGISTER -> id
    PC -> #reg_PC .~ a
    OP1 -> #reg_OP1 .~ a
    OP2 -> #reg_OP2 .~ a

