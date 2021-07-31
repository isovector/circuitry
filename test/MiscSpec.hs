{-# LANGUAGE AllowAmbiguousTypes  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}

module MiscSpec where

import qualified Clash.Sized.Vector as V
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable hiding (sum)
import           Prelude hiding ((.), id, sum)
import           Circuitry.Machinery
import           Test.Hspec

spec :: Spec
spec = do
  traverse_ (it "misc property")
    [ property $ do
        w <- arbitrary @Word8
        pure $ prop_equivalent "constC"
                (constC w)
                (intro w >>> snd')

    , property $ do
        c <- arbitrary @(Circuit Word8 Word8)
        pure $
          prop_equivalent "create >>> first' c >>> destroy = c"
            (create >>> first' c >>> destroy)
            c

    , property $ do
        c <- arbitrary @(Circuit Word8 Word8)
        pure $
          prop_equivalent "create >>> second' c >>> destroy = c"
            (create >>> swap >>> second' c >>> swap >>> destroy)
            c

    , prop_circuit (uncurry (&&)) andGate
    , prop_circuit (not . uncurry (&&)) nandGate
    , prop_circuit not notGate
    , prop_circuit (id &&& id) (copy @Circuit @(Either (Vec 10 Bool) Bool))
    , prop_circuit swap (swap @_ @(Either (Vec 10 Bool) Bool) @Bool)
    , prop_circuit swapE (swapE @_ @(Either (Vec 10 Bool) Bool) @Bool)

    , prop_circuit
        (first' $ V.map not)
        (mapFoldVC @10 $ destroy >>> notGate >>> create)

    , prop_circuit
        (bool 10 127 . fst)
        (ifC (constC @Word8 127) (constC 10))
    , prop_circuit
        (either (const 127) (const 10))
        (eitherE (constC @Word8 127) (constC 10))
    , prop_circuit
        (uncurry B.xor)
        (xorGate)
    ]

prop_circuit
    :: (Arbitrary a, Eq b, Show a, Show b, Reify b, Reify a)
    => (a -> b)
    -> Circuit a b
    -> Property
prop_circuit f c = property $ do
  a <- arbitrary
  t <- arbitrary
  pure $
    counterexample ("time: " <> show t) $
    counterexample ("input: " <> show a) $
      Just (f a) === evalCircuit c a t

prop_equivalent
    :: (Function a, Arbitrary a, Eq b, Show a, Show b, Reify b, Reify a)
    => String
    -> Circuit a b
    -> Circuit a b
    -> Property
prop_equivalent n c1 c2 = property $ do
  forAllShrink arbitrary shrink $ \a  -> do
    t <- resize 5 $ arbitrary
    let c1_r = evalCircuitT c1 (applyFun a) t
        c2_r = evalCircuitT c2 (applyFun a) t
    pure $
      counterexample ("test " <> n) $
      counterexample ("time: " <> show t) $
      counterexample ("c1: " <> show c1_r) $
      counterexample ("c2: " <> show c2_r) $
        c1_r === c2_r

foldrV :: forall n a b r. (a -> r -> (b, r)) -> r -> Vec n a -> (Vec n b, r)
foldrV _ r Nil = (Nil, r)
foldrV f r (Cons a vec) =
  let (b, r') = f a r
      (vec', _) = foldrV f r' vec
   in (Cons b vec', r')

