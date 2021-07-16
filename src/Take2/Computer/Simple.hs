module Take2.Computer.Simple where

{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}

import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Machinery
import           Take2.Primitives (gateDiagram, constantName)
import qualified Yosys as Y



cut :: Embed a => Circuit a ()
cut = create >>> snd'


split :: Circuit Bool (Bool, Bool)
split = copy >>> second' notGate


andV :: KnownNat n => Circuit (Bool, Vec n Bool) (Vec n Bool)
andV = component "andV" $ distribV >>> mapV andGate


pointwise :: (Embed a, Embed b, Embed c, KnownNat n) => Circuit (a, b) c -> Circuit (Vec n a, Vec n b) (Vec n c)
pointwise c = zipVC >>> mapV c


bigAndGate :: (KnownNat n, 1 <= n) => Circuit (Vec n Bool) Bool
bigAndGate
  = shortcircuit (V.foldr (&&) True)
  $ gateDiagram (unaryGateDiagram Y.CellAnd)
  $ create >>> second' (constC True) >>> foldVC andGate


pointwiseAnd
    :: (1 <= m, KnownNat n, KnownNat m)
    => Circuit (Vec m (Vec n Bool)) (Vec n Bool)
pointwiseAnd = transposeV >>> mapV bigAndGate

pointwiseOr
    :: (1 <= m, KnownNat n, KnownNat m)
    => Circuit (Vec m (Vec n Bool)) (Vec n Bool)
pointwiseOr = transposeV >>> mapV bigOrGate


eq :: (Embed a, 1 <= SizeOf a) => Circuit (a, a) Bool
eq = diagrammed (binaryGateDiagram Y.CellEq)
   $ both serial >>> zipVC >>> mapV nxorGate >>> bigAndGate


ifOrEmpty :: (Embed a, Embed b) => Circuit a b -> Circuit (Bool, a) (Vec (SizeOf b) Bool)
ifOrEmpty c = second' (c >>> serial) >>> andV


when
    :: (1 <= SizeOf k, Embed k, Embed v, Embed r, Show k, SeparatePorts k, SeparatePorts v)
    => k
    -> Circuit v r
    -> Circuit (k, v) (Vec (SizeOf r) Bool)
when k c = interface' diagrammed (fmap (mappend "case ") $ constantName k)
           (first' (intro k >>> eq))
       >>> ifOrEmpty c

when'
    :: (1 <= SizeOf k, Embed k, Embed v, Embed r, Show k, SeparatePorts k, SeparatePorts v)
    => k
    -> Circuit (Bool, v) r
    -> Circuit (k, v) (Vec (SizeOf r) Bool)
when' k c = interface' diagrammed (fmap (mappend "case ") $ constantName k)
           (first' (intro k >>> eq))
       >>> c
       >>> serial


onEach :: (Embed a, Embed b, KnownNat cases) => (v -> Circuit a b) -> Vec cases v -> Circuit a (Vec cases b)
onEach f v = sequenceMetaV $ fmap f v


sext
    :: forall n m
     . (KnownNat m, KnownNat n, 1 <= m, (m - 1) <= n)
    => Circuit (Vec m Bool) (Vec n Bool)
sext
    = separate @(m - 1)
  >>> second' (unsafeParse @Bool >>> replicateC @(n - (m - 1)))
  >>> unsafeReinterpret


ext
    :: forall m n
     . (KnownNat m, KnownNat n, m <= n)
    => Circuit (Vec m Bool) (Vec n Bool)
ext = pad False >>> unsafeReinterpret

