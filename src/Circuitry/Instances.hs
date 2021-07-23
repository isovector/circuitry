{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module Circuitry.Instances
  ( module Circuitry.Instances
  , Prim.unsafeReinterpret
  ) where

import Control.Monad (join)
import           Circuitry.Category
import           Circus.DSL
import qualified Circus.Types as Y
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import qualified Data.Aeson as A
import qualified Data.Bits as B
import           Data.Generics.Labels ()
import qualified Data.Map as M
import qualified Data.Text as T
import           GHC.TypeLits
import           GHC.TypeLits.Extra (Max)
import           Prelude hiding ((.), id, sum)
import           Circuitry.Circuit
import           Circuitry.Embed
import           Circuitry.Graph (Graph(Graph), GraphM, synthesizeBits)
import qualified Circuitry.Primitives as Prim
import           Circuitry.Signal (Signal)
import           Test.QuickCheck
import           Type.Reflection (type (:~:) (Refl))
import           Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (fromMaybe)


instance Arbitrary (Signal a b) => Arbitrary (Circuit a b) where
  arbitrary = Circuit <$> pure (error "yo") <*> arbitrary

instance SymmetricProduct Circuit where
  swap = Prim.swap
  reassoc = Prim.unsafeReinterpret
  reassoc' = Prim.unsafeReinterpret

instance MonoidalProduct Circuit where
  (***) = (Prim.***)

instance Cartesian Circuit where
  consume = Prim.consume
  copy = Prim.copy
  fst' = Prim.fst'
  snd' = swap >>> fst'

instance MonoidalSum Circuit where
  (+++) l r = eitherE (l >>> injl) (r >>> injr)
  left = flip (+++) id
  right = (+++) id

instance Distrib Circuit where
  distrib
      :: forall a b c
       . (Embed a, Embed b, Embed c)
      => Circuit (a, Either b c) (Either (a, b) (a, c))
  distrib
      = second' (serial >>> unconsC)
    >>> reassoc
    >>> first' swap
    >>> reassoc'
    >>> second' serial
    >>> consC
    >>> case proveMaxPlusOne @(SizeOf a) @(SizeOf b) @(SizeOf c) of
          Refl -> Prim.unsafeReinterpret

  factor
      :: forall a b c
       . (Embed a, Embed b, Embed c)
      => Circuit (Either (a, b) (a, c)) (a, Either b c)
  factor
      = serial
    >>> unconsC
    >>> second'
        ( (case proveMaxPlusOne @(SizeOf a) @(SizeOf b) @(SizeOf c) of
            Refl -> Prim.unsafeReinterpret
          ) :: Circuit (Vec (Max (SizeOf a + SizeOf b) (SizeOf a + SizeOf c)) Bool)
                       (Vec (SizeOf a) Bool, Vec (Max (SizeOf b) (SizeOf c)) Bool))
    >>> reassoc
    >>> first' swap
    >>> reassoc'
    >>> Prim.unsafeReinterpret


proveMaxPlusOne :: forall a b c. Max b c + a :~: Max (a + b) (a + c)
proveMaxPlusOne = unsafeCoerce Refl
{-# INLINE proveMaxPlusOne #-}


instance SymmetricSum Circuit where
  swapE = serial
      >>> unconsC
      >>> first' notGate
      >>> consC
      >>> unsafeParse

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


instance Cocartesian Circuit where
  injectL = create
        >>> second' (constC False)
        >>> swap
        >>> second' (serial >>> Prim.pad False)
        >>> Prim.unsafeReinterpret
  injectR = create
        >>> second' (constC True)
        >>> swap
        >>> second' (serial >>> Prim.pad False)
        >>> Prim.unsafeReinterpret
  unify = serial
      >>> unconsC
      >>> snd'
      >>> unsafeParse
  tag = Prim.unsafeReinterpret

{-# RULES
"Prim.unsafeReinterpret . Prim.unsafeReinterpret" Prim.unsafeReinterpret . Prim.unsafeReinterpret = Prim.unsafeReinterpret
#-}



raise :: OkCircuit a => Circuit a (Vec 1 a)
raise = Prim.unsafeReinterpret


lower :: OkCircuit a => Circuit (Vec 1 a) a
lower = Prim.unsafeReinterpret


eitherE
    :: (OkCircuit a, OkCircuit b, OkCircuit c)
    => Circuit a c
    -> Circuit b c
    -> Circuit (Either a b) c
eitherE l r = serial
         >>> unconsC
         >>> ifC (separate >>> first' (unsafeParse >>> r) >>> fst')
                 (separate >>> first' (unsafeParse >>> l) >>> fst')


constC :: forall a. (Show a, Embed a) => a -> Circuit () a
constC a = Prim.unsafeReinterpret @_ @(Vec 0 a) >>> Prim.pad a >>> lower


injl :: (OkCircuit a, OkCircuit b) => Circuit a (Either a b)
injl = create
   >>> swap
   >>> (constC False *** (serial >>> Prim.pad False))
   >>> consC
   >>> unsafeParse


injr :: (OkCircuit a, OkCircuit b) => Circuit a (Either b a)
injr = injl >>> swapE


create :: OkCircuit a => Circuit a (a, ())
create = Prim.unsafeReinterpret


destroy :: OkCircuit a => Circuit (a, ()) a
destroy = Prim.unsafeReinterpret


serial :: OkCircuit a => Circuit a (Vec (SizeOf a) Bool)
serial = Prim.unsafeReinterpret


unsafeParse :: OkCircuit a => Circuit (Vec (SizeOf a) Bool) a
unsafeParse = Prim.unsafeReinterpret


consC :: (KnownNat n, OkCircuit a) => Circuit (a, Vec n a) (Vec (n + 1) a)
consC = Prim.unsafeReinterpret


unconsC :: (KnownNat n, OkCircuit a) => Circuit (Vec (n + 1) a) (a, Vec n a)
unconsC = Prim.unsafeReinterpret


separate :: (KnownNat m, KnownNat n, m <= n, OkCircuit a) => Circuit (Vec n a) (Vec m a, Vec (n - m) a)
separate = Prim.unsafeReinterpret


unseparate :: (KnownNat m, KnownNat n, m <= n, OkCircuit a) => Circuit (Vec m a, Vec (n - m) a) (Vec n a)
unseparate = Prim.unsafeReinterpret


ifC :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit a b -> Circuit (Bool, a) b
ifC t f = second' (copy >>> (t *** f))
      >>> distribP
      >>> second' (first' notGate)
      >>> both (swap >>> andAll)
      >>> Prim.zipVC
      >>> mapV orGate
      >>> unsafeParse


andAll :: OkCircuit a => Circuit (a, Bool) (Vec (SizeOf a) Bool)
andAll = swap >>> second' serial >>> distribV >>> mapV andGate


tribufAll :: forall n. KnownNat n => Circuit (Vec n Bool, Bool) (Vec n Bool)
tribufAll = Prim.gateDiagram gr
          $ swap >>> distribV >>> mapV (swap >>> Prim.tribuf)
  where
    gr :: Graph (Vec n Bool, Bool) (Vec n Bool)
    gr = Graph $ \i -> do
      let (i1, i2) = V.splitAtI @n i
      o <- synthesizeBits @(Vec n Bool)
      addCell $
        Y.mkCell Y.CellTribuf $ M.fromList
          [ ("A", (Y.Input, V.toList i1))
          , ("EN", (Y.Input, V.toList i2))
          , ("Y", (Y.Output, V.toList o))
          ]
      pure o


bigOrGate :: (KnownNat n, 1 <= n) => Circuit (Vec n Bool) Bool
bigOrGate
  = Prim.gateDiagram (Prim.unaryGateDiagram Y.CellOr)
  $ create >>> second' (constC False) >>> Prim.foldVC orGate


distribP :: (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit (a, (b, c)) ((a, b), (a, c))
distribP = first' copy
       >>> reassoc'
       >>> second' ( swap
                 >>> reassoc'
                 >>> second' swap
                   )
       >>> reassoc


notGate :: Circuit Bool Bool
notGate
  = Prim.gateDiagram (Prim.unaryGateDiagram Y.CellNot)
  $ copy >>> Prim.nandGate


andGate :: Circuit (Bool, Bool) Bool
andGate
  = Prim.shortcircuit (uncurry (&&))
  $ Prim.gateDiagram (Prim.binaryGateDiagram Y.CellAnd)
  $ Prim.nandGate >>> notGate


orGate :: Circuit (Bool, Bool) Bool
orGate
  = Prim.shortcircuit (uncurry (||))
  $ Prim.gateDiagram (Prim.binaryGateDiagram Y.CellOr)
  $ both notGate >>> Prim.nandGate


norGate :: Circuit (Bool, Bool) Bool
norGate
  = Prim.gateDiagram (Prim.binaryGateDiagram Y.CellNor)
  $ orGate >>> notGate


xorGate :: Circuit (Bool, Bool) Bool
xorGate
  = Prim.shortcircuit (uncurry B.xor)
  $ Prim.gateDiagram (Prim.binaryGateDiagram Y.CellXor)
  $ copy >>> (second' notGate >>> andGate) *** (first' notGate >>> andGate) >>> orGate


nxorGate :: Circuit (Bool, Bool) Bool
nxorGate
  = Prim.gateDiagram (Prim.binaryGateDiagram Y.CellXnor)
  $ xorGate >>> notGate


both :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit (a, a) (b, b)
both f = f *** f


mapV
    :: (KnownNat n, OkCircuit a, OkCircuit b)
    => Circuit a b
    -> Circuit (Vec n a) (Vec n b)
mapV c = create >>> Prim.mapFoldVC (destroy >>> c >>> create) >>> destroy


distribV :: (OkCircuit a, OkCircuit b, KnownNat n) => Circuit (a, Vec n b) (Vec n (a, b))
distribV = first' Prim.cloneV >>> Prim.zipVC


deject :: OkCircuit a => Circuit (Either a a) a
deject = serial >>> unconsC >>> snd' >>> unsafeParse


blackbox
    :: forall a b
     . (SeparatePorts a, SeparatePorts b, Embed a, Embed b)
    => String
    -> Circuit a b
    -> Circuit a b
blackbox = interface' (mkPort "i") (mkPort "o") Prim.unobservable . pure


component
    :: forall a b
     . (SeparatePorts a, SeparatePorts b, Embed a, Embed b)
    => String
    -> Circuit a b
    -> Circuit a b
component = component' (mkPort "i") (mkPort "o")

mkPort :: String -> Int -> Maybe Y.PortName -> Y.PortName
mkPort pre ix = fromMaybe $ Y.PortName $ T.pack $ pre <> show ix


named
    :: forall a b
     . (SeparatePorts a, SeparatePorts b, Embed a, Embed b)
    => String
    -> [String]
    -> [String]
    -> Circuit a b
    -> Circuit a b
named n is os = component' (mk is) (mk os) n
  where
    mk :: [String] -> Int -> Maybe Y.PortName -> Y.PortName
    mk ps i _ = Y.PortName $ T.pack $ (ps <> fmap (show @Int) [0..]) !! i



component'
    :: forall a b
     . (SeparatePorts a, SeparatePorts b, Embed a, Embed b)
    => (Int -> Maybe Y.PortName -> Y.PortName)
    -> (Int -> Maybe Y.PortName -> Y.PortName)
    -> String
    -> Circuit a b
    -> Circuit a b
component' iport oport = interface' iport oport Prim.diagrammed . pure


interface'
    :: forall a b
     . (SeparatePorts a, SeparatePorts b, Embed a, Embed b)
    => (Int -> Maybe Y.PortName -> Y.PortName)
    -> (Int -> Maybe Y.PortName -> Y.PortName)
    -> (Graph a b -> Circuit a b -> Circuit a b)
    -> GraphM String
    -> Circuit a b
    -> Circuit a b
interface' mk_i_port mk_o_port builder get_name = builder $ Graph $ \a -> do
  ab <- synthesizeBits @a
  ip0 <- separatePorts @a
  o <- synthesizeBits @b
  op0 <- separatePorts @b

  let ip = zipWith (\ix -> first' $ mk_i_port ix) [1..] ip0
      op = zipWith (\ix -> first' $ mk_o_port ix) [1..] op0

  name <- get_name
  addCell $
    Y.Cell (Y.CellGeneric $ T.pack name)
      (M.fromList $ fmap (Y.Width *** length) $ ip <> op)
      (M.singleton "name" $ A.String $ T.pack name)
      (M.fromList $ fmap ((, Y.Input) . fst) ip
                 <> fmap ((, Y.Output) . fst) op
      )
      (M.fromList $ ip <> op)
  unifyBits $ M.fromList (zip (join $ fmap snd ip0) $ V.toList ab)
            <> M.fromList (zip (join $ fmap snd op0) $ V.toList o)
  let subst = M.fromList $ V.toList $ V.zip ab a
  unifyBits subst
  pure $ unifyBitsPure subst o


sequenceMetaV
    :: (Embed a, Embed b, KnownNat cases)
    => Vec cases (Circuit a b)
    -> Circuit a (Vec cases b)
sequenceMetaV Nil = create >>> snd' >>> Prim.unsafeReinterpret
sequenceMetaV (Cons c v) = copy >>> first' c >>> second' (sequenceMetaV v) >>> consC

parallelMetaV
    :: (Embed a, Embed b, KnownNat cases)
    => Vec cases (Circuit a b)
    -> Circuit (Vec cases a) (Vec cases b)
parallelMetaV Nil = create >>> snd' >>> Prim.unsafeReinterpret
parallelMetaV (Cons c v) = unconsC >>> c *** parallelMetaV v >>> consC

pointwiseShort
    :: (1 <= m, KnownNat n, KnownNat m)
    => Circuit (Vec m (Vec n Bool)) (Vec n Bool)
pointwiseShort = Prim.transposeV >>> mapV Prim.unsafeShort

pairwiseShort
    :: (KnownNat m)
    => Circuit (Vec m Bool, Vec m Bool) (Vec m Bool)
pairwiseShort = Prim.zipVC >>> mapV (serial >>> Prim.unsafeShort)

intro :: forall b a. (Embed a, Embed b, Show b) => b -> Circuit a (a, b)
intro b = create >>> second' (constC b)

todo :: (Embed a, Embed b) => Circuit a b
todo = create >>> snd' >>> serial >>> Prim.pad False >>> unsafeParse

