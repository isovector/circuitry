module ProductSpec where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Memory
import Take2.Machinery
import Take2.Product (Proj(..))
import Test.Hspec
import Test.Hspec.QuickCheck


data Rec = Rec
  { rec1 :: Word8
  , rec2 :: Bool
  , rec3 :: Word4
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Embed)

instance Arbitrary Rec where
  arbitrary = Rec <$> arbitrary <*> arbitrary <*> arbitrary

deriving anyclass instance Proj Rec "rec1" Word8
deriving anyclass instance Proj Rec "rec2" Bool
deriving anyclass instance Proj Rec "rec3" Word4


spec :: Spec
spec = do
  prop "projects rec1" $ \(rec :: Rec) field ->
    evalCircuit
        (proj #rec1)
        rec { rec1 = field }
        0
      === Just field

  prop "replaces rec1" $ \(rec :: Rec) field ->
    evalCircuit
        (replace #rec1)
        (field, rec)
        0
      === Just rec { rec1 = field }

  prop "projects rec2" $ \(rec :: Rec) field ->
    evalCircuit
        (proj #rec2)
        rec { rec2 = field }
        0
      === Just field

  prop "replaces rec2" $ \(rec :: Rec) field ->
    evalCircuit
        (replace #rec2)
        (field, rec)
        0
      === Just rec { rec2 = field }

  prop "projects rec3" $ \(rec :: Rec) field ->
    evalCircuit
        (proj #rec3)
        rec { rec3 = field }
        0
      === Just field

  prop "replaces rec3" $ \(rec :: Rec) field ->
    evalCircuit
        (replace #rec3)
        (field, rec)
        0
      === Just rec { rec3 = field }


