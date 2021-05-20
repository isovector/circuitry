{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE OverloadedLabels           #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wall                   #-}
{-# OPTIONS_GHC -Wredundant-constraints #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}

module Take2 where

import           Circuitry.Catalyst (Roar(..))
import           Circuitry.Category (Category(..), first', swap, (&&&), (>>>), swapE)
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Lens ((%~), (+~))
import           Control.Monad.State
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable
import           Data.Generics.Labels ()
import           Data.Generics.Wrapped ( _Unwrapped )
import           Data.Typeable
import           Data.Word (Word8)
import           GHC.Generics
import           GHC.TypeLits
import           GHC.TypeLits.Extra
import           Numeric.Natural
import           Prelude hiding ((.), id)
import           Test.QuickCheck


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

copyC :: OkCircuit a => Circuit a (a, a)
copyC = primitive $ raw $ Circuit (genComp "copy") $ Roar $ \f t ->
  let v = f t in v V.++ v

nandGate :: Circuit (Bool, Bool) Bool
nandGate = Circuit (genComp "nand") $ Roar $ \f t -> not . uncurry (&&) $ f t

notGate :: Circuit Bool Bool
notGate = copyC >>> nandGate

andGate :: Circuit (Bool, Bool) Bool
andGate = nandGate >>> notGate

swapC :: forall a b. (OkCircuit a, OkCircuit b) => Circuit (a, b) (b, a)
swapC = primitive $ raw $ Circuit (genComp "swap") $ timeInv $ \v ->
  let (va, vb) = V.splitAtI @(SizeOf a) v
   in vb V.++ va

reassoc :: forall a b c. (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit (a, (b, c)) ((a, b), c)
reassoc = reinterpret

reassoc' :: forall a b c. (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit ((a, b), c) (a, (b, c))
reassoc' = reinterpret

unconsC :: (KnownNat n, OkCircuit a) => Circuit (Vec (n + 1) a) (a, Vec n a)
unconsC = reinterpret

consC :: (KnownNat n, OkCircuit a) => Circuit (a, Vec n a) (Vec (n + 1) a)
consC = reinterpret

firstC :: forall a b c. (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit a b -> Circuit (a, c) (b, c)
firstC c = primitive $ raw $ Circuit undefined $ Roar $ \f t ->
  let v = f t
      (va, vc) = V.splitAtI @(SizeOf a) v
      b = runRoar (c_roar c) (const $ reify va) t
   in embed b V.++ vc

mapVC :: (KnownNat n, OkCircuit a, OkCircuit b, OkCircuit r) => Circuit (a, r) (b, r) -> Circuit (Vec n a, r) (Vec n b, r)
mapVC = undefined

zipVC :: Circuit (Vec n a, Vec n b) (Vec n (a, b))
zipVC = primitive $ Circuit undefined $ timeInv $ uncurry V.zip

primitive :: Circuit a b -> Circuit a b
primitive = id

foldVC :: Circuit (a, b) b -> Circuit (Vec n a, b) b
foldVC c = primitive $ Circuit undefined $ Roar $ \f t ->
  let (v, b) = f t
   in V.foldr (curry $ flip (runRoar (c_roar c)) t . const) b v

-- rightE :: forall a b c. (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit a b -> Circuit (Either c a) (Either c b)
-- rightE c = serial >>> unconsC >>> _

-- ifC :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit a b -> Circuit (Bool, a) b
-- ifC t f = serial >>> unconsC >>> _

type BitsOf a = Vec (SizeOf a) Bool

distrib :: Circuit (a, (b, c)) ((a, b), (a, c))
distrib = undefined


-- cloneAnd :: OkCircuit a => Circuit (Bool, a) (BitsOf a, BitsOf a)
-- cloneAnd = firstC split >>> secondC serial >>> swapC >>> distrib >>> swapC >>> _ >>> zipVC >>>

secondC :: (GenPorts l, GenPorts r, GenPorts b, Embed l, Embed r, Embed b) => Circuit r b -> Circuit (l, r) (l, b)
secondC c = swapC >>> firstC c >>> swapC

-- | a -> (a, not a)
split :: Circuit Bool (Bool, Bool)
split = copyC >>> firstC notGate >>> swapC


serial :: OkCircuit a => Circuit a (Vec (SizeOf a) Bool)
serial = reinterpret

parse :: OkCircuit a => Circuit (Vec (SizeOf a) Bool) a
parse = reinterpret

reinterpret :: (OkCircuit a, OkCircuit b, SizeOf a ~ SizeOf b) => Circuit a b
reinterpret = raw id

introduce :: OkCircuit a => Circuit a (a, ())
introduce = reinterpret

destroy :: OkCircuit a => Circuit (a, ()) a
destroy = reinterpret

swapEC :: (OkCircuit a, OkCircuit b) => Circuit (Either a b) (Either b a)
swapEC = serial >>> unconsC >>> firstC notGate >>> consC >>> parse


timeInv :: (a -> b) -> Roar r a b
timeInv fab = Roar (\ fra -> fab . fra)


prop_circuit :: (Arbitrary a, Eq b, Show b) => (a -> b) -> Circuit a b -> Property
prop_circuit f c = property $ do
  a <- arbitrary
  t <- arbitrary
  pure $ f a === runRoar (c_roar c) (const a) t






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
    , prop_circuit (id &&& id) (copyC @(Either (Vec 10 Bool) Bool))
    , prop_circuit swap (swapC @(Either (Vec 10 Bool) Bool) @Bool)
    , prop_circuit swapE (swapEC @(Either (Vec 10 Bool) Bool) @Bool)
    , prop_circuit (first' (uncurry (&&))) (firstC @_ @_ @Bool andGate)
    ]

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


