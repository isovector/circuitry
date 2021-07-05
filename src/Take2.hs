{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import qualified Clash.Sized.Vector as V
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable hiding (sum)
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Memory
import           Take2.Computer.Simple
import           Take2.Computer.Math
import           Take2.Computer.Examples
import           Take2.Machinery
import           Take2.Primitives (timeInv)



data RW = R | W
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed


alu
    :: (2 <= SizeOf a, SeparatePorts a, Embed a, Numeric a)
    => Circuit (AluOpCode, (a, a)) (Vec (SizeOf a) Bool)
alu =
  branch
    $ Cons (AluOpAdd,     addN >>> fst' >>> serial)
    $ Cons (AluOpAnd,     both serial >>> pointwise andGate)
    $ Cons (AluOpOr,      both serial >>> pointwise orGate)
    $ Cons (AluOpXor,     both serial >>> pointwise xorGate)
    $ Cons (AluOpNot,     fst' >>> serial >>> mapV notGate)
    $ Cons (AluOpShiftL,  fst' >>> shiftL >>> serial)
    $ Cons (AluOpShiftR,  fst' >>> shiftR >>> serial)
    $ Cons (AluOpAShiftR, fst' >>> ashiftR >>> serial)
    $ Nil


data AluOpCode
  = AluOpAdd
  | AluOpAnd
  | AluOpOr
  | AluOpXor
  | AluOpNot
  | AluOpShiftL
  | AluOpShiftR
  | AluOpAShiftR
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed

instance Arbitrary AluOpCode where
  arbitrary
    = let
        terminal
          = [pure AluOpAdd, pure AluOpAnd, pure AluOpOr, pure AluOpXor,
             pure AluOpNot, pure AluOpShiftL, pure AluOpShiftR,
             pure AluOpAShiftR]
       in oneof terminal



prop_circuit :: (Arbitrary a, Eq b, Show a, Show b, Embed b, Embed a) => (a -> b) -> Circuit a b -> Property
prop_circuit f c = property $ do
  a <- arbitrary
  t <- arbitrary
  pure $
    counterexample ("time: " <> show t) $
    counterexample ("input: " <> show a) $
      Just (f a) === evalCircuit c a t

prop_equivalent :: (Function a, Arbitrary a, Eq b, Show a, Show b, Embed b, Embed a) => String -> Circuit a b -> Circuit a b -> Property
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

add2_named
    :: Circuit (Named "A" Bool, (Named "B" Bool, Named "Cin" Bool))
               (Named "Sum" Bool, Named "Cout" Bool)
add2_named = coerceCircuit add2


prop_embedRoundtrip :: forall a. (Show a, Eq a, Embed a, Arbitrary a) => Property
prop_embedRoundtrip = property $ do
  forAllShrink arbitrary shrink $ \(a :: a)  ->
    a === reify (embed a)

prop_eq :: forall a. (1 <= SizeOf a, Show a, Eq a, Embed a, Arbitrary a) => Property
prop_eq = property $ do
  forAllShrink arbitrary shrink $ \(a :: a) -> do
    t <- arbitrary
    pure $ evalCircuit (eq @a) (a, a) t === Just True

example_map :: Circuit (Vec 4 Bool) (Vec 4 Bool)
example_map = mapV (component "" id)


main :: IO ()
main = do
  traverse_ quickCheck
    [
      prop_equivalent "andV"
        (serial >>> intro True >>> swap >>> andV >>> unsafeParse @Word8)
        id

    , property $ do
        prop_equivalent "when"
                (when True id)
                (ifOrEmpty $ id @_ @Bool)

    , prop_circuit (uncurry (==)) $ eq @Bool
    , prop_circuit (uncurry (==)) $ eq @Word8
    , prop_circuit (uncurry (==)) $ eq @(Vec 20 (Bool, Maybe Bool))

    , property $ do
        w <- arbitrary @Word8
        t <- arbitrary
        pure $
          evalCircuit (intro w >>> eq) w t === Just True

    , property $ do
        w <- arbitrary @Word8
        pure $ prop_equivalent "constC"
                (constC w)
                (intro w >>> snd')

    , property $ do
        k <- arbitrary @Word4
        pure $
          prop_equivalent "first' >>> intro"
              (create >>> first' (intro k >>> eq) >>> fst')
              (intro k >>> eq)

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

    , prop_equivalent "inj1 >>> left f >>> deject = f"
        (injl >>> left snap >>> deject)
        (snap)

    , prop_equivalent "mapV snap = snap >>> copy"
        (cloneV @2 >>> mapV snap >>> unsafeReinterpret)
        (snap >>> copy)

    , prop_equivalent "mapV clock = clock >>> copy"
        (cloneV @2 >>> mapV (clock @Word8) >>> unsafeReinterpret)
        (clock @Word8 >>> copy)

    , prop_equivalent "snapN >>> lower = snap"
        (snapN @Bool >>> lower)
        snap

    , prop_equivalent "create >>> first' f >>> destroy = f"
        (create >>> first' rsLatch >>> destroy)
        rsLatch

    , prop_embedRoundtrip @Word4
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

    , evalCircuit (clock @Word8) () 255 === Just 255
    , evalCircuit (clock @Word8) () 256 === Just 0
    ]
  where
    foldrV :: forall n a b r. (a -> r -> (b, r)) -> r -> Vec n a -> (Vec n b, r)
    foldrV _ r Nil = (Nil, r)
    foldrV f r (Cons a vec) =
      let (b, r') = f a r
          (vec', _) = foldrV f r' vec
      in (Cons b vec', r')

