module ProductSpec where

import Prelude hiding ((.), id, sum)
import Circuitry.Machinery
import Test.Hspec
import Test.Hspec.QuickCheck


data Rec = Rec
  { rec1 :: Word8
  , rec2 :: Bool
  , rec3 :: Word4
  , rec4 :: Vec 5 (Either Bool Word2)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Embed, Reify)

instance Arbitrary Rec where
  arbitrary = Rec <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary


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

  prop "projects rec4" $ \(rec :: Rec) field ->
    evalCircuit
        (proj #rec4)
        rec { rec4 = field }
        0
      === Just field

  prop "replaces rec4" $ \(rec :: Rec) field ->
    evalCircuit
        (replace #rec4)
        (field, rec)
        0
      === Just rec { rec4 = field }




