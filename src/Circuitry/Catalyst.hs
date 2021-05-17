{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE RecursiveDo                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wall                   #-}
{-# OPTIONS_GHC -Wno-orphans            #-}
{-# OPTIONS_GHC -Wno-unused-do-bind     #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures #-}

module Circuitry.Catalyst
  ( module Circuitry.Category
  , module Circuitry.Catalyst
  ) where

import           Algebra.Heyting
import           Algebra.Lattice
import           Circuitry.Category
import           Circuitry.GraphViz
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Monad.Writer (tell)
import           Data.Bool (bool)
import           Data.Function (fix)
import           Data.Kind (Type, Constraint)
import           Data.Profunctor.Choice (unleft)
import           Data.Profunctor.Types
import           Data.Typeable (Typeable)
import           GHC.Exts (IsList(..))
import qualified GHC.TypeLits as TL
import           GHC.TypeLits hiding (Nat, KnownNat)
import           Numeric.Natural (Natural)
import           Prelude hiding (id, (.), sum, zip)
import GHC.Generics hiding (S)


data Nat = Z | S Nat

data Vector (n :: Nat) a where
  Empty :: Vector Z a
  (:|) :: a -> Vector n a -> Vector (S n) a

deriving instance Show a => Show (Vector n a)

infixr 3 :|

type family Yo (a :: k) :: Constraint where
  Yo (a :: Type) = PortMapUtils (PortMap a)
  Yo (a :: Nat) = KnownNat a

class KnownNat (n :: Nat) where
  mkVector :: a -> Vector n a

instance KnownNat Z where
  mkVector _ = Empty

instance KnownNat n => KnownNat (S n) where
  mkVector a = a :| mkVector a

class (Typeable a, Yo a) => Stuff (a :: k)
instance (Typeable a, Yo a) => Stuff (a :: k)


type FreeFunction c = Catalyst Stuff c


data CircuitF a b where
  Feedback :: Heyting s => Circuit (a, s) (b, s) -> CircuitF a b
  AndG :: CircuitF (Bool, Bool) Bool
  NandG ::CircuitF (Bool, Bool) Bool
  OrG  :: CircuitF (Bool, Bool) Bool
  NorG :: CircuitF (Bool, Bool) Bool
  XorG :: CircuitF (Bool, Bool) Bool
  NotG :: CircuitF Bool Bool
  Always :: Show a => a -> CircuitF () a

  FoldrV
      :: KnownNat n
      => Circuit () r
      -> Circuit r ()
      -> Circuit (a, r) (b, r)
      -> CircuitF (Vector n a) (Vector n b)
  CloneV :: KnownNat n => CircuitF a (Vector n a)
  ZipV :: KnownNat n => CircuitF (Vector n a, Vector n b) (Vector n (a, b))

  Together :: Circuit a b -> CircuitF a b
  -- Machine :: String -> [String] -> [String] -> Circuit a b -> CircuitF a b
  -- Label :: String -> Circuit a b -> CircuitF a b

deriving instance Show (CircuitF a b)


feedback :: (Stuff a, Stuff b, Stuff s, Heyting s) => Circuit (a, s) (b, s) -> Circuit a b
feedback = liftC . Feedback


andGate :: Circuit (Bool, Bool) Bool
andGate = LiftC AndG

nandGate :: Circuit (Bool, Bool) Bool
nandGate = LiftC NandG


orGate :: Circuit (Bool, Bool) Bool
orGate = LiftC OrG

norGate :: Circuit (Bool, Bool) Bool
norGate = LiftC NorG

xorGate :: Circuit (Bool, Bool) Bool
xorGate = LiftC XorG


notGate :: Circuit Bool Bool
notGate = LiftC NotG

together :: (Stuff a, Stuff b) => Circuit a b -> Circuit a b
together = LiftC . Together

always :: Stuff a => Show a => a -> Circuit () a
always = LiftC . Always




type Circuit = FreeFunction CircuitF


type family PortMap t where
  PortMap () = ()
  PortMap (a, b) = (PortMap a, PortMap b)
  PortMap (Vector Z a) = ()
  PortMap (Vector (S n) a) = PortMap (a, Vector n a)
  PortMap _1 = PortRef


class PortMapUtils t where
  emptyPorts :: Shape -> GraphViz t
  zipConnect :: t -> t -> GraphViz ()

instance PortMapUtils () where
  emptyPorts _ = pure ()
  zipConnect _ _ = pure ()

instance PortMapUtils PortRef where
  emptyPorts sh = do
    ([pr], _) <- component sh ["copy"] []
    pure pr
  zipConnect r1 r2 = do
    connect r1 r2

instance (PortMap (a, b) ~ (PortMap a, PortMap b), PortMapUtils a, PortMapUtils b) => PortMapUtils (a, b) where
  emptyPorts sh = do
    p1 <- emptyPorts @a sh
    p2 <- emptyPorts @b sh
    pure (p1, p2)
  zipConnect (r11, r12) (r21, r22) = do
    zipConnect @a r11 r21
    zipConnect @b r12 r22


raw :: String -> GraphViz ()
raw = tell . pure . Raw


actualize :: forall a b. (PortMapUtils (PortMap a), PortMapUtils (PortMap b), Typeable a) => Circuit a b -> String
actualize c = runGraphViz $ do
  raw "subgraph input {"
  raw "rank=\"source\";"
  inp <- emptyPorts @(PortMap a) Wire
  raw "}"
  z <- compile c inp
  raw "subgraph output {"
  raw "rank=\"sink\";"
  out <- emptyPorts @(PortMap b) Wire
  raw "}"
  zipConnect @(PortMap b) z out



compile :: forall a b. Circuit a b -> PortMap a -> GraphViz (PortMap b)
compile ID i = pure i
compile (Comp cat cat') i = do
  o1 <- compile cat i
  o2 <- compile cat' o1
  pure o2
compile Swap (i1, i2) =
  pure (i2, i1)
compile Reassoc (i1, (i2, i3)) =
  pure ((i1, i2), i3)
compile (First cat) (i1, i2) = do
  o <- compile cat i1
  pure (o, i2)
compile (Second cat) (i1, i2) = do
  o <- compile cat i2
  pure (i1, o)
compile (Alongside cat cat') (i1, i2) = do
  o1 <- compile cat i1
  o2 <- compile cat' i2
  pure (o1, o2)
compile (Fanout cat cat') i = undefined
compile Copy i = do
  a <- emptyPorts @(PortMap a) Point
  zipConnect @(PortMap a) i a
  pure (a, a)
  -- connect i inp
  -- pure out
compile Consume i = undefined
compile Fst (i1, i2 :: x) = do
  -- gr <- emptyPorts @x Ground
  -- zipConnect @x i2 gr
  pure i1
compile Snd (i1 :: x, i2) = do
  -- gr <- emptyPorts @x Ground
  -- zipConnect @x i1 gr
  pure i2
compile SwapE _ = undefined
compile ReassocE _ = undefined
compile (Left' _) _ = undefined
compile (Right' _) _ = undefined
compile (EitherOf _ _) _ = undefined
compile (Fanin _ _) _ = undefined
compile (InjectL) _ = undefined
compile (InjectR) _ = undefined
compile (Unify) _ = undefined
compile Tag _ = undefined
compile (RecurseL _) _ = undefined
compile (RecurseR _) _ = undefined
compile (FixL _) _ = undefined
compile (FixR _) _ = undefined
compile (LiftC (Feedback cat)) i = mdo
  (o, s) <- compile cat (i, s)
  pure o
compile (LiftC AndG) i = liftC2 "and" i
compile (LiftC NandG) i = liftC2 "nand" i
compile (LiftC OrG) i = liftC2 "⦈" i
compile (LiftC NorG) i = liftC2 "nor" i
compile (LiftC XorG) i = liftC2 "xor" i
compile (LiftC NotG) i = do
  ([ai1], [o]) <- component (Record "▷") [""] [""]
  connect i ai1
  pure o
compile (LiftC (Together c)) i = do
  raw "subgraph hi {"
  raw "rank=\"same\";"
  compile c i <* raw "}"
compile (LiftC (FoldrV create destroy each)) i = undefined
compile (LiftC (Always c)) i = undefined
compile Distribute _ = undefined
compile Factor _ = undefined
compile (LiftC ZipV) _ = undefined
compile (LiftC CloneV) i = undefined


liftC2 :: String -> (PortRef, PortRef) -> GraphViz PortRef
liftC2 lbl (i1, i2) = do
  ([ai1, ai2], [o]) <- component (Record lbl) ["", ""] [""]
  connect i1 ai1
  connect i2 ai2
  pure o


newtype Roar r a b = Roar { runRoar :: (r -> a) -> (r -> b) }
  deriving stock Functor

instance Distrib (Roar r) where
  distrib = Roar $ \ f r -> case f r of { (a, e) -> case e of
                                            (Left b) -> Left (a, b)
                                            (Right c) -> Right (a, c) }
  factor = Roar (\ f r -> case f r of
    Left x0 -> case x0 of { (a, b) -> (a, Left b) }
    Right x0 -> case x0 of { (a, c) -> (a, Right c) } )


instance Profunctor (Roar r) where
  lmap fab (Roar f) = Roar (\ fra -> f (fab . fra))
  rmap fbc (Roar f) = Roar (\ fra -> fbc . f fra)

instance Category (Roar r) where
  type Ok (Roar r) = TrivialConstraint
  id = Roar id
  (.) (Roar f) (Roar g) = Roar (f . g)

instance SymmetricProduct (Roar r) where
  swap = Roar (\ f r -> swap $ f r)
  reassoc = Roar (\ f r -> reassoc $ f r)

instance MonoidalProduct (Roar r) where
  first' (Roar f) = Roar $ \rac r ->
     (f (fst . rac) r, snd $ rac r)

instance Cartesian (Roar r) where
  consume = Roar (\ _ _ -> ())
  copy = Roar (\ fra r -> (fra r, fra r))
  fst' = Roar (\ f r -> fst $ f r)
  snd' = Roar (\ f r -> snd $ f r)

instance Fixed (Roar r) where
  fixL (Roar f) = Roar $ \ fra r ->
     fst $ fix $ \(_, s) -> f ((, s) . fra) r
  fixR f = fixL $ swap >>> f >>> swap

instance SymmetricSum (Roar r) where
  swapE = Roar (\ f r -> swapE $ f r)
  reassocE = Roar (\ f r -> reassocE $ f r)

instance MonoidalSum (Roar r) where
  left (Roar f) = Roar $ \ rac r ->
    either (Left . flip f r . const) Right $ rac r

instance Cocartesian (Roar r) where
  injectL = Roar (\ fra r -> Left (fra r))
  injectR = Roar (\ fra r -> Right (fra r))
  unify = Roar (\ f r -> either id id $ f r)
  tag = Roar $ \ f r ->
    let (b, a) = f r
     in case b of
          False -> Left a
          True  -> Right a

instance Recursive (Roar r) where
  recurseL (Roar f) = Roar $ \fra -> unleft $ either (\r -> f (Left . fra) r) Right
  recurseR x = recurseL $ swapE >>> x >>> swapE


arr :: (a -> b) -> Roar r a b
arr fab = Roar (\ fra r -> fab (fra r))


runCircuit :: Circuit a b -> (Natural -> a) -> Natural -> b
runCircuit c ta t = runRoar (lowerCircuit c) ta t

instantCircuit :: Circuit a b -> a -> b
instantCircuit c a = runRoar (lowerCircuit c) (const a) 0


lowerCircuit :: Circuit a b -> Roar Natural a b
lowerCircuit = runFree $ \case
    AndG -> arr $ uncurry (/\)
    OrG  -> arr $ uncurry (\/)
    NandG -> arr $ neg . uncurry (/\)
    NorG  -> arr $ neg . uncurry (\/)
    XorG  -> arr $ neg . uncurry xor
    NotG -> arr neg
    Feedback k ->
      let f = runRoar $ lowerCircuit k
       in Roar $ \tx t -> fst $ loop f tx t
    Together k -> lowerCircuit k
    FoldrV create _ each -> Roar $ \fv t ->
      let v = fv t
          rc = runRoar (lowerCircuit create) (const ()) t
          f = flip (runRoar (lowerCircuit each)) t
       in foldrV (f . const) rc v
    Always c -> Roar $ \ _ _ -> c
    CloneV -> Roar $ \ f nat -> mkVector $ f nat
    ZipV -> Roar $ \f n -> uncurry zipV $ f n






xor :: Bool -> Bool -> Bool
xor False False = False
xor False True = True
xor True False = True
xor True True = False


loop
    :: Heyting s
    => ((Natural -> (x, s)) -> Natural -> (y, s))
    -> (Natural -> x)
    -> Natural
    -> (y, s)
loop f tx 0 = f ((, bottom) . tx) 0
loop f tx t =
  let (_, s) = loop f tx $ t - 1
   in f ((, s) . tx) t



reassoc' :: (AllOk k [a, b, c], MonoidalProduct k, SymmetricProduct k) => ((a, b), c) `k` (a, (b, c))
reassoc' = first' swap >>> swap >>> reassoc >>> swap >>> second' swap


spike :: Natural -> Natural -> Bool
spike n t = bool False True $ n == t


---


instance IsList (Vector Z a) where
  type Item (Vector Z a) = a
  fromList _ = Empty
  toList _ = []

instance (IsList (Vector n a), Item (Vector n a) ~ a) => IsList (Vector (S n) a) where
  type Item (Vector (S n) a) = a
  fromList (a : as) = a :| fromList as
  fromList [] = error "not enough elements for IsList Vector"
  toList (a :| as) = a : toList as


zipV :: Vector n a -> Vector n b -> Vector n (a, b)
zipV Empty Empty = Empty
zipV (a' :| vec) (b' :| vec') = (a', b') :| zipV vec vec'


-- foldrC
--     :: Circuit () r
--     -> Circuit r ()
--     -> Circuit a (b, r)
--     -> Circuit (Vector n a) (Vector n b)
-- foldrC create destroy one = recurseL $ peel >>> _

foldrV :: ((a, r) -> (b, r)) -> r -> Vector n a -> Vector n b
foldrV _ _ Empty = Empty
foldrV f r (a :| vec) =
  let (b, r') = f (a, r)
   in b :| foldrV f r' vec



pairwise :: (Stuff a, Stuff b, Stuff c) => Circuit (a, (b, c)) ((a, b), ((a, c), (b, c)))
pairwise = (reassoc >>> fst')
       &&& ((second' swap >>> reassoc >>> fst') &&& snd')


distribP :: (Stuff a, Stuff b, Stuff c) => Circuit (a, (b, c)) ((a, b), (a, c))
distribP
    = (reassoc >>> fst')
  &&& (second' swap >>> reassoc >>> fst')


paired :: (Stuff a, Stuff b, Stuff c) => Circuit (a, (b, c)) ((a, b), (b, c))
paired
    = (reassoc >>> fst') &&& snd'


cout :: Circuit ((Bool, Bool), Bool) Bool
cout = reassoc'
   >>> pairwise
   >>> andGate *** (andGate *** andGate)
   >>> paired
   >>> orGate *** orGate
   >>> orGate


sum :: Circuit ((Bool, Bool), Bool) Bool
sum = first' xorGate >>> xorGate


add :: Circuit ((Bool, Bool), Bool) (Bool, Bool)
add = sum &&& cout


type One = S Z
type Two = S One
type Three = S Two
type Four = S Three

#define PMU(n,a) PortMapUtils (PortMap (Vector n a))


addN :: (Stuff n, PMU(n,(Bool)), PMU(n,(Bool,Bool))) => Circuit (Vector n (Bool, Bool)) (Vector n Bool)
addN = LiftC $ FoldrV (always False) consume add


split :: Circuit Bool (Bool, Bool)
split = id &&& notGate


demux2 :: (Show a, Heyting a, Stuff a) => Circuit (a, Bool) (Either a a)
demux2 = swap >>> tag


introduce :: Stuff a => Circuit a (a, ())
introduce = id &&& consume


mux2 :: Stuff a => Circuit (Either a a) a
mux2 = unify

hold :: Circuit Bool Bool
hold = feedback $ orGate >>> copy

clock :: Circuit () Bool
clock = feedback $ snd' >>> notGate >>> copy

rsLatch :: Circuit (Bool, Bool) Bool
rsLatch = feedback $ reassoc' >>> second' norGate >>> norGate >>> copy


shuffle :: (Stuff a, Stuff b, Stuff c, Stuff d) => Circuit ((a, b), (c, d)) ((a, c), (b, d))
shuffle = reassoc &&& (second' swap >>> reassoc)
      >>> (   (fst' >>> reassoc' >>> second' snd')
          *** (fst' >>> first' snd'))

snap :: Circuit (Bool, Bool) Bool
snap = (copy *** (split >>> swap)) >>> shuffle >>> (andGate *** andGate) >>> rsLatch

clone :: (PMU(n,a), Stuff n, Stuff a) => Circuit a (Vector n a)
clone = LiftC CloneV

zip :: (PMU(n,a), PMU(n,b), PMU(n,(a,b)), Stuff n, Stuff a, Stuff b) => Circuit (Vector n a, Vector n b) (Vector n (a, b))
zip = LiftC ZipV

snapN :: (PMU(n,Bool), PMU(n,(Bool,Bool)), Stuff n) => Circuit (Bool, Vector n Bool) (Vector n Bool)
snapN = first' clone >>> zip >>> LiftC (FoldrV consume consume $ first' snap)


snapping :: Natural -> (Bool, Bool)
snapping n@3 = (True, odd n)
snapping n@6 = (True, odd n)
snapping n = (False, odd n)

snappingN :: KnownNat n => Natural -> (Bool, Vector n Bool)
snappingN n@3 = (True, mkVector $ odd n)
snappingN n@6 = (True, mkVector $ odd n)
snappingN n = (False, mkVector $ odd n)



class GEmbedable (f :: Type -> Type) where
  type GSize f :: TL.Nat
  gembed :: f x -> Vec (GSize f) Bool
  greify :: Vec (GSize f) Bool -> f x

instance GEmbedable U1 where
  type GSize U1 = 0
  gembed _ = Nil
  greify _ = U1

instance Embeddable a => GEmbedable (K1 _1 a) where
  type GSize (K1 _1 a) = Size a
  gembed = embed . unK1
  greify = K1 . reify

instance GEmbedable f => GEmbedable (M1 _1 _2 f) where
  type GSize (M1 _1 _2 f) = GSize f
  gembed = gembed . unM1
  greify = M1 . greify

instance (GEmbedable f, GEmbedable g, TL.KnownNat (GSize f)) => GEmbedable (f :*: g) where
  type GSize (f :*: g) = GSize f + GSize g
  gembed (f :*: g) = gembed f V.++ gembed g
  greify v =
    let (va, vb) = V.splitAtI v
     in greify va :*: greify vb

instance
    (GEmbedable f, GEmbedable g, TL.KnownNat (GSize f), TL.KnownNat (GSize g))
      => GEmbedable (f :+: g)
    where
  type GSize (f :+: g) = GSize f + GSize g + 1
  gembed (L1 f) = False :> gembed f V.++ V.repeat @(GSize g) False
  gembed (R1 g) = True :> V.repeat @(GSize f) False V.++ gembed g
  greify (t :> v) =
    case t of
      False -> L1 $ greify $ V.takeI v
      True  -> R1 $ greify $ V.dropI @(GSize f) v



class Embeddable a where
  type Size a :: TL.Nat
  type Size a = GSize (Rep a)

  embed :: a -> Vec (Size a) Bool
  default embed
      :: (GSize (Rep a) ~ Size a, Generic a, GEmbedable (Rep a))
      => a -> Vec (Size a) Bool
  embed = gembed . from

  reify :: Vec (Size a) Bool -> a
  default reify
     :: (GSize (Rep a) ~ Size a, Generic a, GEmbedable (Rep a))
     => Vec (Size a) Bool -> a
  reify = to . greify


instance Embeddable ()

instance Embeddable Bool

instance
    (Embeddable a, Embeddable b, TL.KnownNat (Size a))
      => Embeddable (a, b)

instance
    (Embeddable a, Embeddable b, TL.KnownNat (Size a), TL.KnownNat (Size b))
      => Embeddable (Either a b)

