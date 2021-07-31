{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module EmbedSpec where

import Data.Proxy
import Data.Typeable
import Prelude hiding ((.), id, sum)
import Circuitry.Machinery
import Test.Hspec
import Test.Hspec.QuickCheck


data EnumTest = ET1 | ET2 | ET3 | ET4 | ET5 | ET6 | ET7
  deriving stock (Enum, Bounded, Generic, Show, Eq, Ord)
  deriving (Embed, Reify, Arbitrary) via (EmbededEnum EnumTest)


spec :: Spec
spec = do
   prop_embedRoundtrip @Word4
   prop_embedRoundtrip @()
   prop_embedRoundtrip @Bool
   prop_embedRoundtrip @Word8
   prop_embedRoundtrip @(Either Bool ())
   prop_embedRoundtrip @(Either () ())
   prop_embedRoundtrip @(Either (Either Bool Bool) (Either Bool Bool))
   prop_embedRoundtrip @(Vec 10 Bool)
   prop_embedRoundtrip @(Vec 10 (Vec 10 Bool))
   prop_embedRoundtrip @(Vec 10 (Either Bool Bool))
   prop_embedRoundtrip @(Vec 10 (Either Bool Bool))
   prop_embedRoundtrip @EnumTest


prop_embedRoundtrip :: forall a. (Typeable a, Show a, Eq a, Reify a, Arbitrary a) => SpecWith ()
prop_embedRoundtrip = prop ("embed/reify for " <> show (typeRep $ Proxy @a)) $ do
  forAllShrink arbitrary shrink $ \(a :: a)  ->
    a === reify (embed a)

