{-# LANGUAGE AllowAmbiguousTypes                    #-}
{-# LANGUAGE CPP                                    #-}
{-# LANGUAGE DataKinds                              #-}
{-# LANGUAGE DefaultSignatures                      #-}
{-# LANGUAGE DeriveFunctor                          #-}
{-# LANGUAGE DeriveGeneric                          #-}
{-# LANGUAGE DerivingStrategies                     #-}
{-# LANGUAGE FlexibleContexts                       #-}
{-# LANGUAGE FlexibleInstances                      #-}
{-# LANGUAGE GADTs                                  #-}
{-# LANGUAGE GADTs                                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving             #-}
{-# LANGUAGE InstanceSigs                           #-}
{-# LANGUAGE LambdaCase                             #-}
{-# LANGUAGE MultiParamTypeClasses                  #-}
{-# LANGUAGE NoStarIsType                           #-}
{-# LANGUAGE OverloadedLists                        #-}
{-# LANGUAGE PolyKinds                              #-}
{-# LANGUAGE RecursiveDo                            #-}
{-# LANGUAGE ScopedTypeVariables                    #-}
{-# LANGUAGE StandaloneDeriving                     #-}
{-# LANGUAGE TupleSections                          #-}
{-# LANGUAGE TypeApplications                       #-}
{-# LANGUAGE TypeFamilies                           #-}
{-# LANGUAGE TypeOperators                          #-}
{-# LANGUAGE UndecidableInstances                   #-}
{-# LANGUAGE UndecidableSuperClasses                #-}

{-# OPTIONS_GHC -Wall                               #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-do-bind                 #-}
{-# OPTIONS_GHC -Wno-orphans #-}

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
import           Control.Arrow (first)
import           Control.Monad.Writer (tell)
import           Data.Bool (bool)
import           Data.Function (fix, on)
import           Data.Kind (Type, Constraint)
import           Data.Profunctor.Choice (unleft)
import           Data.Profunctor.Types
import           Data.Typeable (Typeable)
import           Data.Word (Word8)
import           GHC.Generics hiding (S)
import           GHC.TypeLits
import           Numeric.Natural (Natural)
import           Prelude hiding (id, (.), sum, zip)
import           Test.QuickCheck (CoArbitrary, Testable (property), Arbitrary (arbitrary), counterexample, applyFun, Function (function), functionMap, forAllShrink, shrink, (===), quickCheck)
import           Test.QuickCheck.Arbitrary (CoArbitrary(coarbitrary))
import           Test.QuickCheck.Checkers
import qualified Data.Bits as B
import Test.QuickCheck.Property (Property)
import Debug.Trace (trace)
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)



instance (Show a, EqProp b, Arbitrary a, Show b) => EqProp (Circuit a b) where
  (=-=) = (=-=) `on` lowerCircuit

instance Arbitrary Natural where
  arbitrary = fmap (fromIntegral . abs @Integer) arbitrary

instance CoArbitrary Natural where
  coarbitrary = coarbitrary @Integer . fromIntegral

instance Function Natural where
  function = functionMap fromIntegral (fromIntegral @Integer . abs)

instance (Show a, EqProp b, CoArbitrary r, Arbitrary a, Arbitrary r, Show r, Show b, Function r) => EqProp (Roar r a b) where
  Roar r1 =-= Roar r2 = property $ do
    t <- arbitrary
    pure $ forAllShrink arbitrary shrink $ \f' -> do
    let f = applyFun f'
        v1 = r1 f t
        v2 = r2 f t
    counterexample (show t) $ counterexample (show v1) $ counterexample (show v2) $ v1 =-= v2


embedTest :: forall a. (Eq a, Show a, Arbitrary a, Embeddable a) => Property
embedTest = property $ do
  a <- arbitrary @a
  pure $ counterexample (show a) $ a === reify (embed a)

instance EqProp Word8 where
  (=-=) = (===)


addressable1Test :: Property
addressable1Test = property $ do
  f <- arbitrary @(Time -> (Bool, (Bool, Word8)))
  t <- arbitrary
  pure $
    runCircuit (addressable1 snapN) ((t, ) . f)
      =-=
        runCircuit snapN f

addressableTest :: Property
addressableTest = property $ do
  f <- arbitrary @(Time -> (Bool, (Bool, Word8)))
  t <- arbitrary @Bool
  pure $
    runCircuit (addressable snapN) ((V.singleton t, ) . f)
      =-=
        runCircuit snapN f

main :: IO ()
main = quickCheck addressableTest






type family Yo (a :: k) :: Constraint where
  Yo (a :: Type) = (() :: Constraint)
  Yo (a :: Nat) = KnownNat a

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
  Debug :: Show a => CircuitF a a

  MapStateV
      :: KnownNat n
      => Circuit (a, r) (b, r)
      -> CircuitF (Vec n a, r) (Vec n b, r)
  FoldrV :: Circuit (a, b) b -> CircuitF (Vec n a, b) b
  CloneV :: KnownNat n => CircuitF a (Vec n a)
  ZipV :: KnownNat n => CircuitF (Vec n a, Vec n b) (Vec n (a, b))

  Together :: Circuit a b -> CircuitF a b
  Embed :: Embeddable a => CircuitF a (Vec (Size a) Bool)
  Reify :: Embeddable a => CircuitF (Vec (Size a) Bool) a

  MapMaybe :: Circuit a b -> CircuitF (Maybe a) (Maybe b)
  ConsV :: CircuitF (a, Vec n a) (Vec (n + 1) a)
  Uncons :: CircuitF (Vec (n + 1) a) (a, Vec n a)

  Cross
      :: (KnownNat (2 ^ (n + 1)))
      => Circuit (a, a) a
      -> CircuitF (Vec (n + 1) (a, a)) (Vec (2 ^ (n + 1)) a)


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

data PortMap t where
  NoPortMap :: PortMap ()
  Pair :: PortMap a -> PortMap b -> PortMap (a, b)
  VecPM :: KnownNat n => Vec n (PortMap a) -> PortMap (Vec n a)
  Ref :: PortRef -> PortMap a


-- type family PortMap t where
--   PortMap () = ()
--   PortMap (a, b) = (PortMap a, PortMap b)
--   PortMap (Vec 0 a) = ()
--   PortMap (Vec (n + 1) a) = PortMap (a, Vec n a)
--   PortMap _1 = PortRef


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


-- actualize :: forall a b. (PortMapUtils (PortMap a), PortMapUtils (PortMap b), Typeable a) => Circuit a b -> String
-- actualize c = runGraphViz $ do
--   raw "subgraph input {"
--   raw "rank=\"source\";"
--   inp <- emptyPorts @(PortMap a) Wire
--   raw "}"
--   z <- compile c inp
--   raw "subgraph output {"
--   raw "rank=\"sink\";"
--   out <- emptyPorts @(PortMap b) Wire
--   raw "}"
--   zipConnect @(PortMap b) z out



-- compile :: forall a b. Circuit a b -> PortMap a -> GraphViz (PortMap b)
-- compile ID i = pure i
-- compile (Comp cat cat') i = do
--   o1 <- compile cat i
--   o2 <- compile cat' o1
--   pure o2
-- compile Swap (i1, i2) =
--   pure (i2, i1)
-- compile Reassoc (i1, (i2, i3)) =
--   pure ((i1, i2), i3)
-- compile (First cat) (i1, i2) = do
--   o <- compile cat i1
--   pure (o, i2)
-- compile (Second cat) (i1, i2) = do
--   o <- compile cat i2
--   pure (i1, o)
-- compile (Alongside cat cat') (i1, i2) = do
--   o1 <- compile cat i1
--   o2 <- compile cat' i2
--   pure (o1, o2)
-- compile (Fanout cat cat') i = undefined
-- compile Copy i = do
--   a <- emptyPorts @(PortMap a) Point
--   zipConnect @(PortMap a) i a
--   pure (a, a)
--   -- connect i inp
--   -- pure out
-- compile Consume i = undefined
-- compile Fst (i1, i2 :: x) = do
--   -- gr <- emptyPorts @x Ground
--   -- zipConnect @x i2 gr
--   pure i1
-- compile Snd (i1 :: x, i2) = do
--   -- gr <- emptyPorts @x Ground
--   -- zipConnect @x i1 gr
--   pure i2
-- compile SwapE _ = undefined
-- compile ReassocE _ = undefined
-- compile (Left' _) _ = undefined
-- compile (Right' _) _ = undefined
-- compile (EitherOf _ _) _ = undefined
-- compile (Fanin _ _) _ = undefined
-- compile (InjectL) _ = undefined
-- compile (InjectR) _ = undefined
-- compile (Unify) _ = undefined
-- compile Tag _ = undefined
-- compile (RecurseL _) _ = undefined
-- compile (RecurseR _) _ = undefined
-- compile (FixL _) _ = undefined
-- compile (FixR _) _ = undefined
-- compile (LiftC (Feedback cat)) i = mdo
--   (o, s) <- compile cat (i, s)
--   pure o
-- compile (LiftC AndG) i = liftC2 "and" i
-- compile (LiftC NandG) i = liftC2 "nand" i
-- compile (LiftC OrG) i = liftC2 "⦈" i
-- compile (LiftC NorG) i = liftC2 "nor" i
-- compile (LiftC XorG) i = liftC2 "xor" i
-- compile (LiftC NotG) i = do
--   ([ai1], [o]) <- component (Record "▷") [""] [""]
--   connect i ai1
--   pure o
-- compile (LiftC (Together c)) i = do
--   raw "subgraph hi {"
--   raw "rank=\"same\";"
--   compile c i <* raw "}"
-- compile (LiftC (MapStateV create destroy each)) i = undefined
-- compile (LiftC (Always c)) i = undefined
-- compile Distribute _ = undefined
-- compile Factor _ = undefined
-- compile (LiftC ZipV) _ = undefined
-- compile (LiftC CloneV) i = undefined


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


runCircuit :: Circuit a b -> (Time -> a) -> Time -> b
runCircuit c ta t = runRoar (lowerCircuit c) ta t

instantCircuit :: Circuit a b -> a -> b
instantCircuit c a = runRoar (lowerCircuit c) (const a) 0


lowerCircuit :: Circuit a b -> Roar Time a b
lowerCircuit = runFree $ \case
    AndG -> arr $ uncurry (/\)
    OrG  -> arr $ uncurry (\/)
    NandG -> arr $ neg . uncurry (/\)
    NorG  -> arr $ neg . uncurry (\/)
    XorG  -> arr $ neg . uncurry xor
    NotG -> arr neg
    Feedback k ->
      let f = runRoar $ lowerCircuit k
       in Roar $ \tx t -> fst $ loop bottom f tx t
    Together k -> lowerCircuit k
    MapStateV each -> Roar $ \fv t ->
      let (v, r) = fv t
          f = flip (runRoar (lowerCircuit each)) t
       in foldrV (f . const) r v
    Always c -> Roar $ \ _ _ -> c
    CloneV -> Roar $ \ f nat -> V.repeat $ f nat
    ZipV -> Roar $ \f n -> uncurry zipV $ f n
    Embed -> Roar $ \f n -> embed $ f n
    Reify -> Roar $ \f n -> reify $ f n
    Cross c -> Roar $ \f n ->
      let v = f n
          c' = flip (runRoar (lowerCircuit c)) n
       in crossV (curry $ c' . const) v
    FoldrV c -> Roar $ \f n ->
      let (v, r) = f n
          c' = flip (runRoar (lowerCircuit c)) n
       in V.foldr (curry $ c' . const) r v
    Debug -> Roar $ \f n -> trace (show $ f n) $ f n
    MapMaybe m -> Roar $ \f n ->
      let v = f n
          m' = flip (runRoar (lowerCircuit m)) n
       in fmap (m' . const) v
    Uncons -> Roar $ \f n -> uncons $ f n
    ConsV -> Roar $ \f n -> uncurry (:>) $ f n

uncons :: Vec (n + 1) a1 -> (a1, Vec n a1)
uncons (a :> v) = (a, v)
uncons _ = error "impossible"




ifC :: Stuff a => Circuit a a -> Circuit (Bool, a) a
ifC c = tag >>> id ||| c





xor :: Bool -> Bool -> Bool
xor False False = False
xor False True = True
xor True False = True
xor True True = False


loop
    :: s
    -> ((Time -> (x, s)) -> Time -> (y, s))
    -> (Time -> x)
    -> Time
    -> (y, s)
loop b f tx 0 = f ((, b) . tx) 0
loop b f tx t =
  let (_, s) = loop b f tx $ t - 1
   in f ((, s) . tx) t



reassoc' :: (AllOk k [a, b, c], MonoidalProduct k, SymmetricProduct k) => ((a, b), c) `k` (a, (b, c))
reassoc' = first' swap >>> swap >>> reassoc >>> swap >>> second' swap


spike :: Time -> Time -> Bool
spike n t = bool False True $ n == t


---



zipV :: Vec n a -> Vec n b -> Vec n (a, b)
zipV = V.zip


-- foldrC
--     :: Circuit () r
--     -> Circuit r ()
--     -> Circuit a (b, r)
--     -> Circuit (Vec n a) (Vec n b)
-- foldrC create destroy one = recurseL $ peel >>> _

foldrV :: ((a, r) -> (b, r)) -> r -> Vec n a -> (Vec n b, r)
foldrV _ r Nil = (Nil, r)
foldrV f r (Cons a vec) =
  let (b, r') = f (a, r)
   in first (b :>) $ foldrV f r' vec



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


type One = 1
type Two = 2
type Three = 3
type Four = 4

#define PMU(n,a) PortMapUtils (PortMap (Vec n a))


addN :: (Stuff n, PMU(n,(Bool)), PMU(n,(Bool,Bool))) => Circuit (Vec n (Bool, Bool)) (Vec n Bool)
addN = introduce >>> second' (always False) >>> LiftC (MapStateV add) >>> fst'


split :: Circuit Bool (Bool, Bool)
split = id &&& notGate


demux2 :: (Show a, Heyting a, Stuff a) => Circuit (a, Bool) (Either a a)
demux2 = swap >>> tag

-- newtype Addr n =

-- memory :: Circuit (Vector n Bool


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

-- S
-- V
snap :: Circuit (Bool, Bool) Bool
snap = (copy *** (split >>> swap)) >>> shuffle >>> (andGate *** andGate) >>> rsLatch

clone :: (Stuff n, Stuff a) => Circuit a (Vec n a)
clone = LiftC CloneV

zip :: (Stuff n, Stuff a, Stuff b) => Circuit (Vec n a, Vec n b) (Vec n (a, b))
zip = LiftC ZipV

snapN :: (Embeddable a, KnownNat (Size a), Stuff a) => Circuit (Bool, a) a
snapN = second' (LiftC Embed)
    >>> first' clone
    >>> zip
    >>> liftV snap
    >>> LiftC Reify


liftV :: (Stuff n, Stuff a, Stuff b) => Circuit a b -> Circuit (Vec n a) (Vec n b)
liftV c = introduce >>> LiftC (MapStateV $ first' c) >>> fst'


snapping :: Time -> (Bool, Bool)
snapping n@3 = (True, odd n)
snapping n@6 = (True, odd n)
snapping n = (False, odd n)

type Time = Natural

snappingN :: Time -> (Bool, (Bool, Word8))
snappingN n = (False, (n < 256, fromIntegral $ n `mod` 255))


type Addr n = Vec n Bool


singleton :: Stuff a => Circuit a (Vec 1 a)
singleton = clone


addressable1
    :: (Stuff a, Stuff b, Embeddable b, KnownNat (Size b))
    => Circuit a b
    -> Circuit (Bool, a) b
addressable1 c
    = first' split
  >>> swap
  >>> distribP
  >>> yo *** yo
  >>> zip
  >>> liftV orGate
  >>> LiftC Reify
  where
    yo = ((c >>> LiftC Embed) *** clone)
     >>> zip
     >>> liftV andGate

distribV :: (Stuff a, Stuff b, KnownNat n) => Circuit (a, Vec n b) (Vec n (a, b))
distribV = swap >>> LiftC (MapStateV $ swap >>> (id &&& fst')) >>> fst'


debug :: (Stuff a, Show a) => Circuit a a
debug = liftC Debug


-- TODO(sandy): unsafe coercion! but it WORKS
coerceBoolAMaybeA
    :: forall a. (Stuff a, KnownNat (Size a), KnownNat (1 + Size a), Embeddable a)
    => Circuit (Bool, a) (Maybe a)
coerceBoolAMaybeA  = case proofNPlus1 @(Size a) of Refl -> LiftC Embed >>> LiftC Reify


address
    :: forall n a
     . (KnownNat (Size a), Embeddable a, Show a, KnownNat (n + 1), Stuff a, KnownNat (2 ^ (n + 1)), KnownNat (1 + Size a))
    => Circuit (Addr (n + 1), a)
               (Vec (2 ^ (n + 1)) (Maybe a))
address
    = first' (liftV split >>> liftC (Cross andGate))
  >>> swap
  >>> distribV
  >>> liftV (swap >>> coerceBoolAMaybeA)


proofNPlus1 :: 1 + a :~: a + 1
proofNPlus1 = unsafeCoerce Refl



addressable
    :: (Embeddable a, Show a, KnownNat (n + 1), Stuff a, Stuff b, Embeddable b, KnownNat (Size b), KnownNat (2 ^ (n + 1)), KnownNat (Size a), KnownNat (1 + Size a), KnownNat (Size b + 1))
    => Circuit a b
    -> Circuit (Addr (n + 1), a) b
addressable c
    = address
  -- TODO(sandy): bug! we need to and-gate first!
  >>> liftV (liftC (MapMaybe c) >>> liftC Embed)
  >>> introduce
  >>> second' (always False >>> clone)
  >>> liftC (FoldrV $ zip >>> liftV orGate)
  >>> liftC Uncons
  >>> snd'
  >>> liftC Reify


addressableSnapping :: Time -> (Bool, (Bool, Bool))
addressableSnapping n@3 = (False, (True, odd n))
addressableSnapping n@5 = (True, (True, odd n))
addressableSnapping n = (n `mod` 3 == 0, (False, odd n))




class GEmbedable (f :: Type -> Type) where
  type GSize f :: Nat
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

instance (GEmbedable f, GEmbedable g, KnownNat (GSize f)) => GEmbedable (f :*: g) where
  type GSize (f :*: g) = GSize f + GSize g
  gembed (f :*: g) = gembed f V.++ gembed g
  greify v =
    let (va, vb) = V.splitAtI v
     in greify va :*: greify vb

-- TODO(sandy): stupid instance; should overlap bits
instance
    (GEmbedable f, GEmbedable g, KnownNat (GSize f), KnownNat (GSize g))
      => GEmbedable (f :+: g)
    where
  type GSize (f :+: g) = GSize f + GSize g + 1
  gembed (L1 f) = False :> gembed f V.++ V.repeat @(GSize g) False
  gembed (R1 g) = True :> V.repeat @(GSize f) False V.++ gembed g
  greify (t :> v) =
    case t of
      False -> L1 $ greify $ V.takeI v
      True  -> R1 $ greify $ V.dropI @(GSize f) v
  greify _ = error "imppossible"


cross :: (a -> a -> a) -> [(a, a)] -> [a]
cross _ [] = []
cross _ [(a, b)] = [a, b]
cross f ((a, b) : as) =
  let c = cross f as
   in fmap (f a) c <> fmap (f b) c


crossV
    :: (KnownNat (2 ^ (n + 1)))
    => (a -> a -> a)
    -> Vec (n + 1) (a, a)
    -> Vec (2 ^ (n + 1)) a
crossV f = V.unsafeFromList . cross f . V.toList
  -- where
  --   go Nil = Nil
  --   go (Cons (a, b) vec) =
  --     let vec' = go vec
  --     in V.map (f a) vec' V.++ V.map (f b) vec'



-- pairwiseV :: (Stuff a, Stuff b, KnownNat n) => Circuit (Vec n (a, b)) (Vec (2 ^ n) (a, b))
-- pairwiseV = copy >>> liftC (MapStateV $ _) >>> snd'


class Embeddable a where
  type Size a :: Nat
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

instance (KnownNat (Size a), Embeddable a) => Embeddable (Maybe a)

instance
    (Embeddable a, Embeddable b, KnownNat (Size a))
      => Embeddable (a, b)

instance
    (Embeddable a, Embeddable b, KnownNat (Size a), KnownNat (Size b))
      => Embeddable (Either a b)

instance (KnownNat n, Embeddable a, KnownNat (Size a)) => Embeddable (Vec n a) where
  type Size (Vec n a) = n * Size a
  embed = V.concatMap embed
  reify = V.map reify . V.unconcatI

instance Embeddable Word8 where
  type Size Word8 = 8
  embed w8 =
    let t = B.testBit w8
     in t 0 :> t 1 :> t 2 :> t 3 :> t 4 :> t 5 :> t 6 :> t 7 :> Nil
  reify (b0 :> b1 :> b2 :> b3 :> b4 :> b5 :> b6 :> b7 :> Nil) =
    let s b = B.shiftL (bool 0 1 b)
     in foldr @[] (B..|.) 0 $ zipWith s [b0, b1, b2, b3, b4, b5, b6, b7] [0..]
  reify _ = error "impossible"

