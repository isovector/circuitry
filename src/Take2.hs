{-# LANGUAGE AllowAmbiguousTypes  #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

{-# OPTIONS_GHC -Wall                   #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Main where

import qualified Clash.Sized.Vector as V
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable hiding (sum)
import           Data.Generics.Labels ()
import           Data.Word (Word8)
import           Prelude hiding ((.), id, sum)
import           Take2.Circuit
import           Take2.Embed
import           Take2.Machinery
import           Take2.Numeric
import           Take2.Primitives (timeInv, shortcircuit)
import           Test.QuickCheck


everyPair
    :: (OkCircuit a, OkCircuit b, OkCircuit c)
    => Circuit (a, (b, c))
               ((a, b), ((a, c), (b, c)))
everyPair = (reassoc >>> fst')
       &&& ((second' swap >>> reassoc >>> fst') &&& snd')


cout :: Circuit (Bool, (Bool, Bool)) Bool
cout = everyPair
   >>> andGate *** (andGate *** andGate)
   >>> ((reassoc >>> fst') &&& snd')
   >>> orGate *** orGate
   >>> orGate


sum :: Circuit (Bool, (Bool, Bool)) Bool
sum = second' xorGate >>> xorGate


-- input: A B Cin
-- output: S Cout
add2 :: Circuit (Bool, (Bool, Bool)) (Bool, Bool)
add2 = copy >>> sum *** cout


addN :: (Numeric a, OkCircuit a) => Circuit (a, a) (a, Bool)
addN = shortcircuit (uncurry addNumeric)
     $ serial *** serial
   >>> zipVC
   >>> create
   >>> second' (constC False)
   >>> mapFoldVC (reassoc' >>> add2)
   >>> first' unsafeParse


split :: Circuit Bool (Bool, Bool)
split = copy >>> second' notGate


hold :: Circuit Bool Bool
hold = fixC False $ orGate >>> copy


tickTock :: Circuit () Bool
tickTock = fixC False $ snd' >>> copy >>> second' notGate


clock :: forall a. (OkCircuit a, Numeric a) => Circuit () a
clock = fixC (zero @a) $ first' (constC one)
                     >>> swap
                     >>> first' copy
                     >>> reassoc'
                     >>> second' (addN >>> fst')


-- input: R S
rsLatch :: Circuit (Bool, Bool) Bool
rsLatch = fixC False $ reassoc' >>> second' norGate >>> norGate >>> copy


-- input: S V
snap :: Circuit (Bool, Bool) Bool
snap = second' (split >>> swap)
   >>> distrib
   >>> both andGate
   >>> rsLatch

snapN :: OkCircuit a => Circuit (Bool, a) (Vec (SizeOf a) Bool)
snapN = second' serial >>> distribV >>> mapV snap


prop_circuit :: (Arbitrary a, Eq b, Show a, Show b) => (a -> b) -> Circuit a b -> Property
prop_circuit f c = property $ do
  a <- arbitrary
  t <- arbitrary
  pure $
    counterexample ("time: " <> show t) $
    counterexample ("input: " <> show a) $
      f a === evalCircuit c t a

prop_equivalent :: (Function a, Arbitrary a, Eq b, Show a, Show b) => Circuit a b -> Circuit a b -> Property
prop_equivalent c1 c2 = property $ do
  forAllShrink arbitrary shrink $ \a  -> do
    t <- resize 5 $ arbitrary
    let c1_r = evalCircuitT c1 (applyFun a) t
        c2_r = evalCircuitT c2 (applyFun a) t
    pure $
      counterexample ("time: " <> show t) $
      counterexample ("c1: " <> show c1_r) $
      counterexample ("c2: " <> show c2_r) $
        c1_r === c2_r


prop_embedRoundtrip :: forall a. (Show a, Eq a, Embed a, Arbitrary a) => Property
prop_embedRoundtrip = property $ do
  forAllShrink arbitrary shrink $ \(a :: a)  ->
    a === reify (embed a)


main :: IO ()
main = do
  traverse_ quickCheck
    [ property $ do
        c <- arbitrary @(Circuit Word8 Word8)
        pure $ prop_equivalent (create >>> first' c >>> destroy) c

    , property $ do
        c <- arbitrary @(Circuit Word8 Word8)
        pure $ prop_equivalent
                 (create >>> swap >>> second' c >>> swap >>> destroy)
                 c

    , prop_equivalent (create >>> first' rsLatch >>> destroy) rsLatch

    , prop_embedRoundtrip @()
    , prop_embedRoundtrip @Bool
    , prop_embedRoundtrip @Word8
    , prop_embedRoundtrip @(Either Bool ())
    , prop_embedRoundtrip @(Either () ())
    , prop_embedRoundtrip @(Either (Either Bool Bool) (Either Bool Bool))
    , prop_embedRoundtrip @(Vec 10 Bool)
    , prop_embedRoundtrip @(Vec 10 (Vec 10 Bool))
    , prop_embedRoundtrip @(Vec 10 (Either Bool Bool))

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
        (\(v, r0) -> foldrV @10 (\(a :: Bool) r -> (a B..&. r, B.xor a r)) r0 v)
        (mapFoldVC $ Circuit undefined $ timeInv $ \(a, r) ->
            (a B..&. r, B.xor a r))
    , prop_circuit
        (bool 10 127 . fst)
        (ifC (constC @Word8 127) (constC 10))
    , prop_circuit
        (either (const 127) (const 10))
        (eitherE (constC @Word8 127) (constC 10))
    , prop_circuit
        (uncurry B.xor)
        (xorGate)
    , prop_circuit
        (\(a, (b, c)) -> (a `B.xor` b `B.xor` c, (fromEnum a + fromEnum b + fromEnum c) >= 2))
        add2
    , prop_circuit
        (uncurry (+))
        (addN @Word8 >>> fst')
    ]
  where
    foldrV :: forall n a b r. (a -> r -> (b, r)) -> r -> Vec n a -> (Vec n b, r)
    foldrV _ r Nil = (Nil, r)
    foldrV f r (Cons a vec) =
      let (b, r') = f a r
          (vec', _) = foldrV f r' vec
      in (Cons b vec', r')

