{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE OverloadedLabels           #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

{-# OPTIONS_GHC -Wall                   #-}
{-# OPTIONS_GHC -Wredundant-constraints #-}
{-# OPTIONS_GHC -Wno-unused-imports     #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Take2 where

import           Circuitry.Catalyst (Roar(..), loop)
import           Circuitry.Category (Category(..), first', swap, (&&&), (>>>), swapE, SymmetricProduct (reassoc), MonoidalProduct (second'), Cartesian(..), SymmetricSum(..), MonoidalSum)
import           Circuitry.Category (MonoidalProduct(..))
import           Circuitry.Category (MonoidalSum(..))
import           Circuitry.Category (SymmetricProduct(..))
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Lens ((%~), (+~))
import           Control.Monad.State
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable hiding (sum)
import           Data.Generics.Labels ()
import           Data.Generics.Wrapped ( _Unwrapped )
import           Data.Typeable
import           Data.Word (Word8, Word16, Word32, Word64)
import           GHC.Generics
import           GHC.TypeLits
import           GHC.TypeLits.Extra
import           Numeric.Natural
import           Prelude hiding ((.), id, sum)
import           Test.QuickCheck
import           Unsafe.Coerce (unsafeCoerce)


newtype Port = Port { getPort :: Int }
  deriving stock Generic

data Ports p t where
  UnitP :: Ports () t
  BoolP :: t -> Ports Bool t
  PairP :: Ports a t -> Ports b t -> Ports (a, b) t
  VectorP :: (KnownNat n) => Vec n (Ports a t) -> Ports (Vec n a) t
  EitherP
      :: MaxProof (SizeOf a) (SizeOf b)
      -> t
      -> Ports (Vec (Max (SizeOf a) (SizeOf b)) Bool) t
      -> Ports (Either a b) t

data BiggerThan (n :: Nat) a b where
  BiggerThan
        :: (n ~ Bigger a b, KnownNat na, KnownNat nb, (SizeOf a + na) ~ n, (SizeOf b + nb) ~ n)
        => BiggerThan n a b


data Circuit a b = Circuit
  { c_graph :: Graph a b
  , c_roar :: Roar Natural a b
  }

class (Stuff a, Embed a) => OkCircuit a
instance (Stuff a, Embed a) => OkCircuit a

instance Category Circuit where
  type Ok Circuit = OkCircuit
  id = Circuit id id
  Circuit gg gr . Circuit fg fr = Circuit (gg . fg) (gr . fr)

raw :: (OkCircuit a, OkCircuit b) => Circuit (Vec (SizeOf a) Bool) (Vec (SizeOf b) Bool) -> Circuit a b
raw c = Circuit (genComp "unravel" >>> c_graph c >>> genComp "ravel") $
  Roar $ \f t ->
    let x = runRoar (c_roar c) (fmap embed f)
     in reify $ x t

nandGate :: Circuit (Bool, Bool) Bool
nandGate = Circuit (genComp "nand") $ Roar $ \f t -> not . uncurry (&&) $ f t

notGate :: Circuit Bool Bool
notGate = copy >>> nandGate

andGate :: Circuit (Bool, Bool) Bool
andGate = nandGate >>> notGate

orGate :: Circuit (Bool, Bool) Bool
orGate = both notGate >>> nandGate

xorGate :: Circuit (Bool, Bool) Bool
xorGate = dup >>> (second' notGate >>> andGate) *** (first' notGate >>> andGate) >>> orGate

swapC :: forall a b. (OkCircuit a, OkCircuit b) => Circuit (a, b) (b, a)
swapC = primitive $ raw $ Circuit (genComp "swap") $ timeInv $ \v ->
  let (va, vb) = V.splitAtI @(SizeOf a) v
   in vb V.++ va

reassoc' :: forall a b c. (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit ((a, b), c) (a, (b, c))
reassoc' = unsafeReinterpret

unconsC :: (KnownNat n, OkCircuit a) => Circuit (Vec (n + 1) a) (a, Vec n a)
unconsC = unsafeReinterpret

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
add2 = dup >>> sum *** cout


class Numeric a

instance Numeric Bool
instance Numeric Word8
instance Numeric Word16
instance Numeric Word32
instance Numeric Word64
instance Numeric (Vec n Bool)


addN :: (Numeric a, OkCircuit a) => Circuit (a, a) (a, Bool)
addN = serial *** serial
   >>> zipVC
   >>> create
   >>> second' (constC False)
   >>> mapFoldVC (reassoc' >>> add2)
   >>> first' unsafeParse

fixC :: s -> Circuit (a, s) (b, s) -> Circuit a b
fixC s k = primitive $ Circuit undefined $
  let f = runRoar $ c_roar k
    in Roar $ \tx t -> fst $ loop s f tx t

inductionV
    :: forall n r a
     . KnownNat n
      => Circuit (Vec 0 a) r
    -> (forall x. KnownNat x => Circuit (Vec (x + 1) a) r)
    -> Circuit (Vec n a) r
inductionV nil plus = primitive $ Circuit undefined $ Roar $ \f t ->
  let v = f t
   in case natVal $ Proxy @n of
        0 -> runRoar (c_roar nil) (const $ unsafeCoerce v) t
        _ -> runRoar (c_roar $ plus @n) (const $ unsafeCoerce v) t


consC :: (KnownNat n, OkCircuit a) => Circuit (a, Vec n a) (Vec (n + 1) a)
consC = unsafeReinterpret

cloneV :: KnownNat n => Circuit r (Vec n r)
cloneV = primitive $ Circuit undefined $ timeInv V.repeat

mapFoldVC
    :: (KnownNat n, OkCircuit a, OkCircuit b, OkCircuit r)
    => Circuit (a, r) (b, r)
    -> Circuit (Vec n a, r) (Vec n b, r)
mapFoldVC c = primitive $ Circuit undefined $ Roar $ \f t ->
  let (v, r0) = f t
   in case v of
        Nil -> (Nil, r0)
        Cons a v_cons ->
          let (b, r') = runRoar (c_roar c) (const (a, r0)) t
              (v', _) = runRoar (c_roar $ mapFoldVC c) (const (v_cons, r')) t
           in (Cons b v', r')

mapV
    :: (KnownNat n, OkCircuit a, OkCircuit b)
    => Circuit a b
    -> Circuit (Vec n a) (Vec n b)
mapV c = create >>> mapFoldVC (destroy >>> c >>> create) >>> destroy


pad
    :: forall m n a
     . (KnownNat m, KnownNat n, m <= n)
    => a
    -> Circuit (Vec m a) (Vec n a)
pad a = primitive $ Circuit undefined $ timeInv $ \v -> V.repeat @(n - m) a V.++ v


zipVC :: Circuit (Vec n a, Vec n b) (Vec n (a, b))
zipVC = primitive $ Circuit undefined $ timeInv $ uncurry V.zip

primitive :: Circuit a b -> Circuit a b
primitive = id

foldVC :: Circuit (a, b) b -> Circuit (Vec n a, b) b
foldVC c = primitive $ Circuit undefined $ Roar $ \f t ->
  let (v, b) = f t
   in V.foldr (curry $ flip (runRoar (c_roar c)) t . const) b v


eitherE
    :: (OkCircuit a, OkCircuit b, OkCircuit c)
    => Circuit a c
    -> Circuit b c
    -> Circuit (Either a b) c
eitherE l r = serial
         >>> unconsC
         >>> ifC (separate >>> first' (unsafeParse >>> r) >>> fst')
                 (separate >>> first' (unsafeParse >>> l) >>> fst')


injl :: (OkCircuit a, OkCircuit b) => Circuit a (Either a b)
injl = create
   >>> swap
   >>> (constC False *** (serial >>> pad False))
   >>> consC
   >>> unsafeParse

injr :: (OkCircuit a, OkCircuit b) => Circuit a (Either b a)
injr = injl >>> swapE


bimapE
    :: (OkCircuit a, OkCircuit b, OkCircuit a', OkCircuit b')
    => Circuit a a'
    -> Circuit b b'
    -> Circuit (Either a b) (Either a' b')
bimapE l r = eitherE (l >>> injl) (r >>> injr)


unsafeCoerceC
    :: (KnownNat n, SizeOf a <= n, OkCircuit a)
    => Circuit a a
    -> Circuit (Vec n Bool) (Vec n Bool)
unsafeCoerceC c = separate
              >>> first' (unsafeParse >>> c >>> serial)
              >>> unseparate

dup :: OkCircuit a => Circuit a (a, a)
dup = cloneV >>> unsafeReinterpret


both :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit (a, a) (b, b)
both f = f *** f

ifC :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit a b -> Circuit (Bool, a) b
ifC t f = second' (dup >>> (t *** f))
      >>> distrib
      >>> second' (first' notGate)
      >>> both (second' serial >>> distribV >>> mapV andGate)
      >>> zipVC
      >>> mapV orGate
      >>> unsafeParse

type BitsOf a = Vec (SizeOf a) Bool

distrib :: (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit (a, (b, c)) ((a, b), (a, c))
distrib = first' dup
      >>> reassoc'
      >>> second' ( swap
                >>> reassoc'
                >>> second' swap
                  )
      >>> reassoc

distribV :: (OkCircuit a, OkCircuit b, KnownNat n) => Circuit (a, Vec n b) (Vec n (a, b))
distribV = first' cloneV >>> zipVC

raise :: OkCircuit a => Circuit a (Vec 1 a)
raise = unsafeReinterpret

lower :: OkCircuit a => Circuit (Vec 1 a) a
lower = unsafeReinterpret

-- cloneAnd :: OkCircuit a => Circuit (Bool, a) (BitsOf a, BitsOf a)
-- cloneAnd = first' split >>> second' serial >>> swapC >>> distrib >>> swapC >>> _ >>> zipVC >>>

-- | a -> (a, not a)
split :: Circuit Bool (Bool, Bool)
split = copy >>> first' notGate >>> swapC


serial :: OkCircuit a => Circuit a (Vec (SizeOf a) Bool)
serial = unsafeReinterpret

unsafeParse :: OkCircuit a => Circuit (Vec (SizeOf a) Bool) a
unsafeParse = unsafeReinterpret

unsafeReinterpret :: (OkCircuit a, OkCircuit b, SizeOf a ~ SizeOf b) => Circuit a b
unsafeReinterpret = raw id

separate :: (KnownNat m, KnownNat n, m <= n, OkCircuit a) => Circuit (Vec n a) (Vec m a, Vec (n - m) a)
separate = unsafeReinterpret

unseparate :: (KnownNat m, KnownNat n, m <= n, OkCircuit a) => Circuit (Vec m a, Vec (n - m) a) (Vec n a)
unseparate = unsafeReinterpret

create :: OkCircuit a => Circuit a (a, ())
create = unsafeReinterpret

destroy :: OkCircuit a => Circuit (a, ()) a
destroy = unsafeReinterpret

swapEC :: (OkCircuit a, OkCircuit b) => Circuit (Either a b) (Either b a)
swapEC = serial >>> unconsC >>> first' notGate >>> consC >>> unsafeParse


timeInv :: (a -> b) -> Roar r a b
timeInv fab = Roar (\ fra -> fab . fra)


prop_circuit :: (Arbitrary a, Eq b, Show a, Show b) => (a -> b) -> Circuit a b -> Property
prop_circuit f c = property $ do
  a <- arbitrary
  t <- arbitrary
  pure $
    counterexample ("time: " <> show t) $
    counterexample ("input: " <> show a) $
      f a === evalCircuit c t a

evalCircuit :: Circuit a b -> Natural -> a -> b
evalCircuit c t a = runRoar (c_roar c) (const a) t


constC :: a -> Circuit () a
constC a = primitive $ Circuit undefined $ timeInv $ const a


instance SymmetricProduct Circuit where
  swap = swapC
  reassoc = unsafeReinterpret

instance MonoidalProduct Circuit where
  first' c = primitive $ raw $ Circuit (genComp "first'") $ Roar $ \f t ->
    let v = f t
        (va, vc) = V.splitAtI v
        b = runRoar (c_roar c) (const $ reify va) t
    in embed b V.++ vc
  second' c = swapC >>> first' c >>> swapC

instance Cartesian Circuit where
  consume = primitive $ raw $ Circuit (genComp "consume") $ timeInv $ const Nil
  copy = primitive $ raw $ Circuit (genComp "copy") $ timeInv $ \v -> v V.++ v
  fst' = primitive $ raw $ Circuit (genComp "fst") $ timeInv V.takeI
  snd' = primitive $ raw $ Circuit (genComp "snd") $ timeInv V.dropI

instance SymmetricSum Circuit where
  swapE = swapEC

  reassocE = undefined
  -- reassocE :: forall a b c. (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit
  --               (Either a (Either b c))
  --               (Either (Either a b) c)
  -- reassocE = primitive $ raw $ Circuit (genComp "snd") $
  --   case (maxProof @a @(Either b c), maxProof @b @c, maxProof @(Either a b) @c) of
  --     (MaxProof, MaxProof, MaxProof) -> timeInv $ \(t1 :> v) ->
  --       case t1 of
  --         False -> let a = reify @a $ V.takeI @(SizeOf a) v
  --                   in embed (Left (Left a) :: Either (Either a b) c)
  --         True ->
  --           case v of
  --             (False :> v') ->
  --               let b = reify @b $ V.takeI @(SizeOf b) v'
  --               in embed (Left (Right b) :: Either (Either a b) c)
  --             (True :> v') ->
  --               let c = reify @c $ V.takeI @(SizeOf c) v'
  --               in embed (Right c :: Either (Either a b) c)
  --             _ -> error "impossible"


-- reassocF :: Either (Either a b) c -> Either a (Either b c)
-- reassocF (Left (Left a)) = Left a
-- reassocF (Left (Right b)) = Right (Left b)
-- reassocF (Right c) = Right (Right c)

instance MonoidalSum Circuit where
  (+++) = bimapE
  right = bimapE id






prop_embedRoundtrip :: forall a. (Show a, Eq a, Embed a, Arbitrary a) => Property
prop_embedRoundtrip = property $ do
  a <- arbitrary @a
  pure $ a === reify (embed a)

main :: IO ()
main = do
  traverse_ quickCheck
    [ prop_embedRoundtrip @()
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
    , prop_circuit swap (swapC @(Either (Vec 10 Bool) Bool) @Bool)
    , prop_circuit swapE (swapEC @(Either (Vec 10 Bool) Bool) @Bool)
    -- , prop_circuit (first' (uncurry (&&))) (first' andGate)
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

foldrV :: forall n a b r. (a -> r -> (b, r)) -> r -> Vec n a -> (Vec n b, r)
foldrV _ r Nil = (Nil, r)
foldrV f r (Cons a vec) =
  let (b, r') = f a r
      (vec', _) = foldrV f r' vec
   in (Cons b vec', r')

class KnownNat (SizeOf a) => Embed a where
  type SizeOf a :: Nat
  type SizeOf a = GSizeOf (Rep a)
  embed :: a -> Vec (SizeOf a) Bool
  default embed :: (SizeOf a ~ GSizeOf (Rep a), GEmbed (Rep a), Generic a) => a -> Vec (SizeOf a) Bool
  embed = gembed . from
  reify :: Vec (SizeOf a) Bool -> a
  default reify :: (SizeOf a ~ GSizeOf (Rep a), GEmbed (Rep a), Generic a) => Vec (SizeOf a) Bool -> a
  reify = to . greify


class KnownNat (GSizeOf f) => GEmbed f where
  type GSizeOf f :: Nat
  gembed :: f x -> Vec (GSizeOf f) Bool
  greify :: Vec (GSizeOf f) Bool -> f x

instance GEmbed f => GEmbed (M1 _1 _2 f) where
  type GSizeOf (M1 _1 _2 f) = GSizeOf f
  gembed (M1 fx) = gembed fx
  greify = M1 . greify

instance GEmbed U1 where
  type GSizeOf U1 = 0
  gembed U1 = Nil
  greify _ = U1

instance Embed a => GEmbed (K1 _1 a) where
  type GSizeOf (K1 _1 a) = SizeOf a
  gembed = embed . unK1
  greify = K1 . reify

instance (GEmbed f, GEmbed g) => GEmbed (f :*: g) where
  type GSizeOf (f :*: g) = GSizeOf f + GSizeOf g
  gembed (f :*: g) = gembed f V.++ gembed g
  greify v =
    let (a, b) = V.splitAtI v
     in greify a :*: greify b

instance (GEmbed f, GEmbed g) => GEmbed (f :+: g) where
  type GSizeOf (f :+: g) = Max (GSizeOf f) (GSizeOf g) + 1
  gembed (L1 f) =
    case maxProof' @(GSizeOf f) @(GSizeOf g) of
      MaxProof -> False :> (gembed f V.++ V.repeat False)
  gembed (R1 g) =
    case maxProof' @(GSizeOf f) @(GSizeOf g) of
      MaxProof -> True :> (gembed g V.++ V.repeat False)
  greify (t :> v) =
    case maxProof' @(GSizeOf f) @(GSizeOf g) of
      MaxProof ->
        case t of
          False -> L1 $ greify $ V.takeI v
          True  -> R1 $ greify $ V.takeI v
  greify _ = error "impossible"


instance Embed ()
instance Embed a => Embed (Maybe a)

instance GenPorts Word8 where
  genPorts = undefined

instance Embed Word8 where
  type SizeOf Word8 = 8
  embed w8 =
    let t = B.testBit w8
     in t 0 :> t 1 :> t 2 :> t 3 :> t 4 :> t 5 :> t 6 :> t 7 :> Nil
  reify (b0 :> b1 :> b2 :> b3 :> b4 :> b5 :> b6 :> b7 :> Nil) =
    let s b = B.shiftL (bool 0 1 b)
     in foldr @[] (B..|.) 0 $ zipWith s [b0, b1, b2, b3, b4, b5, b6, b7] [0..]
  reify _ = error "impossible"

instance Embed Bool

instance (Embed a, Embed b) => Embed (a, b)

instance (Embed a, KnownNat n) => Embed (Vec n a) where
  type SizeOf (Vec n a) = n * SizeOf a
  embed = V.concatMap embed
  reify = V.map reify . V.unconcatI

instance (Embed a, Embed b) => Embed (Either a b)


data MaxProof a b where
  MaxProof :: (KnownNat na, KnownNat nb, Max a b ~ (a + na), Max a b ~ (b + nb)) => MaxProof a b

maxProof :: (KnownNat (SizeOf a), KnownNat (SizeOf b)) => MaxProof (SizeOf a) (SizeOf b)
maxProof = maxProof'

maxProof' :: forall a b. (KnownNat a, KnownNat b) => MaxProof a b
maxProof' =
  let a = natVal $ Proxy @a
      b = natVal $ Proxy @b
      m = max a b
      na = m - a
      nb = m - b
   in withSomeNat na $ \(_ :: Proxy na) ->
      withSomeNat nb $ \(_ :: Proxy nb) ->
        case sameNat (Proxy @(Max a b)) (Proxy @(a + na)) of
          Just Refl ->
            case sameNat (Proxy @(Max a b)) (Proxy @(b + nb)) of
              Just Refl -> MaxProof
              Nothing -> error "impossible failure to synthesize MaxProof"
          Nothing -> error "impossible failure to synthesize MaxProof"


withSomeNat :: Integer -> (forall n. KnownNat n => Proxy n -> r) -> r
withSomeNat i f =
  case someNatVal i of
   Nothing -> error "don't be an idiot"
   Just (SomeNat n) -> f n


type Bigger a b = Max (SizeOf a) (SizeOf b)


instance Functor (Ports p) where
  fmap _ UnitP = UnitP
  fmap fab (BoolP a) = BoolP (fab a)
  fmap fab (PairP po' po_ba) = PairP (fmap fab po') (fmap fab po_ba)
  fmap fab (VectorP v) = VectorP $ fmap (fmap fab) v
  fmap fab (EitherP proof t p) = EitherP proof (fab t) $ fmap fab p


class (GenPorts a, KnownNat (SizeOf a)) => Stuff a
instance (GenPorts a, KnownNat (SizeOf a)) => Stuff a



instance Category Graph where
  type Ok Graph = Stuff
  id = Graph pure
  Graph g . Graph f = Graph (g <=< f)

-- instance SymmetricProduct Graph where
--   swap = genComp "swap"
--   reassoc = genComp "reassoc"

-- instance MonoidalProduct Graph where
--   first' _ = Graph $ \(PairP p bp) -> do
--     cout <- mkComp "first" p
--     pure $ PairP cout bp

-- instance Cartesian Graph where
--   consume = genComp "consume"
--   copy = genComp "copy"
--   fst' = genComp "fst"
--   snd' = genComp "snd"



class GenPorts a where
  genPorts :: GraphM (Ports a Port)

instance GenPorts () where
  genPorts = pure UnitP

instance GenPorts Bool where
  genPorts = fmap BoolP freshPort

instance (GenPorts a, GenPorts b) => GenPorts (a, b) where
  genPorts = PairP <$> genPorts <*> genPorts

instance (GenPorts a, KnownNat n) => GenPorts (Vec n a) where
  genPorts = fmap VectorP $ V.traverse# id $ V.repeat genPorts

instance (Stuff a, Stuff b, KnownNat (Bigger a b)) => GenPorts (Either a b) where
  genPorts = EitherP <$> pure (maxProof @a @b) <*> freshPort <*> genPorts




newtype Graph a b = Graph
  { unGraph :: Ports a Port -> GraphM (Ports b Port)
  }

genComp :: GenPorts b => String -> Graph a b
genComp = Graph . mkComp


mkComp :: GenPorts b => String -> Ports a Port -> GraphM (Ports b Port)
mkComp name pa = do
  pb <- genPorts
  modify $ #gs_components %~ (Component name pa pb :)
  pure pb


data Component t where
  Component :: String -> Ports a t -> Ports b t -> Component t


freshPort :: GraphM Port
freshPort = do
  p <- gets gs_next_port
  modify $ #gs_next_port . _Unwrapped +~ 1
  pure p


data GraphState = GraphState
  { gs_next_port :: Port
  , gs_components :: [Component Port]
  }
  deriving stock (Generic)

newtype GraphM a = GraphM { unGraphM :: State GraphState a }
  deriving newtype (Functor, Applicative, Monad, MonadState GraphState)


