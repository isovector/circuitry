{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Primitives where

import           Circuitry.Catalyst (Roar(..), loop)
import           Circuitry.Category (Category(..), (>>>))
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Monad.State
import           Data.Generics.Labels ()
import           GHC.TypeLits
import           Prelude hiding ((.), id, sum)
import           Take2.Embed
import           Take2.Graph
import           Take2.Circuit


primitive :: Circuit a b -> Circuit a b
primitive = id


timeInv :: (a -> b) -> Roar r a b
timeInv fab = Roar (\ fra -> fab . fra)


raw :: (OkCircuit a, OkCircuit b) => Circuit (Vec (SizeOf a) Bool) (Vec (SizeOf b) Bool) -> Circuit a b
raw c = Circuit (genComp "unravel" >>> c_graph c >>> genComp "ravel") $
  Roar $ \f t ->
    let x = runRoar (c_roar c) (fmap embed f)
     in reify $ x t


swap :: forall a b. (OkCircuit a, OkCircuit b) => Circuit (a, b) (b, a)
swap =
  primitive $ raw $ Circuit (genComp "swap") $ timeInv $ \v ->
    let (va, vb) = V.splitAtI @(SizeOf a) v
    in vb V.++ va


first' :: (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit a b -> Circuit (a, c) (b, c)
first' c =
  primitive $ raw $ Circuit (genComp "first'") $ Roar $ \f t ->
    let v = f t
        (va, vc) = V.splitAtI v
        b = runRoar (c_roar c) (const $ reify va) t
    in embed b V.++ vc


consume :: OkCircuit a => Circuit a ()
consume = primitive $ raw $ Circuit (genComp "consume") $ timeInv $ const Nil


copy :: OkCircuit a => Circuit a (a, a)
copy = primitive $ raw $ Circuit (genComp "copy") $ timeInv $ \v -> v V.++ v


fst' :: (OkCircuit a, OkCircuit b) => Circuit (a, b) a
fst' = primitive $ raw $ Circuit (genComp "fst") $ timeInv V.takeI


constC :: a -> Circuit () a
constC a = primitive $ Circuit undefined $ timeInv $ const a


pad
    :: forall m n a
     . (KnownNat m, KnownNat n, m <= n)
    => a
    -> Circuit (Vec m a) (Vec n a)
pad a = primitive $ Circuit undefined $ timeInv $ \v -> V.repeat @(n - m) a V.++ v


nandGate :: Circuit (Bool, Bool) Bool
nandGate = primitive $ Circuit (genComp "nand") $ timeInv $ not . uncurry (&&)


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


zipVC :: Circuit (Vec n a, Vec n b) (Vec n (a, b))
zipVC = primitive $ Circuit undefined $ timeInv $ uncurry V.zip


cloneV :: KnownNat n => Circuit r (Vec n r)
cloneV = primitive $ Circuit undefined $ timeInv V.repeat


fixC :: s -> Circuit (a, s) (b, s) -> Circuit a b
fixC s k = primitive $ Circuit undefined $
  let f = runRoar $ c_roar k
    in Roar $ \tx t -> fst $ loop s f tx t


foldVC :: Circuit (a, b) b -> Circuit (Vec n a, b) b
foldVC c = primitive $ Circuit undefined $ Roar $ \f t ->
  let (v, b) = f t
   in V.foldr (curry $ flip (runRoar (c_roar c)) t . const) b v
