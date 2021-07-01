{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}

module Take2.Primitives where

import           Circuitry.Catalyst (loop, Time, Signal (..), primSignal)
import           Circuitry.Category (Category(..), (>>>))
import qualified Circuitry.Category as Category
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Monad.State
import           Data.Generics.Labels ()
import           Data.Proxy
import           Data.Type.Equality
import           Debug.RecoverRTTI (anythingToString)
import           Debug.Trace (trace)
import           GHC.TypeLits
import           Prelude hiding ((.), id, sum)
import           Take2.Circuit
import           Take2.Embed
import           Take2.Graph
import           Unsafe.Coerce (unsafeCoerce)
import Data.Profunctor (dimap, lmap)


primitive :: Circuit a b -> Circuit a b
primitive = id


timeInv :: (a -> b) -> Signal a b
timeInv = primSignal
{-# INLINE timeInv #-}


raw :: (OkCircuit a, OkCircuit b) => Circuit (Vec (SizeOf a) Bool) (Vec (SizeOf b) Bool) -> Circuit a b
raw c = Circuit (genComp "unravel" >>> c_graph c >>> genComp "ravel") $
  Signal $ \a ->
    let (sf, sb) = pumpSignal (c_roar c) $ embed a
     in (dimap embed reify sf, reify sb)


swap :: forall a b. (OkCircuit a, OkCircuit b) => Circuit (a, b) (b, a)
swap =
  primitive $ raw $ Circuit (genComp "swap") $ timeInv $ \v ->
    let (va, vb) = V.splitAtI @(SizeOf a) v
    in vb V.++ va


(***) :: (OkCircuit a, OkCircuit b, OkCircuit a', OkCircuit b') => Circuit a a' -> Circuit b b' -> Circuit (a, b) (a', b')
(***) l r =
  primitive $ raw $ Circuit (genComp "***") $
    timeInv V.splitAtI >>> (Category.***) (timeInv reify >>> c_roar l >>> timeInv embed)
                                          (timeInv reify >>> c_roar r >>> timeInv embed)
                       >>> timeInv (uncurry (V.++))


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


---- induction :: (KnownNat n, OkCircuit a => Circuit (Vec n a) (Either (Vec 0 a) (a, Vec (n - 1) a))
---- induction = primitive $ Circuit undefined $
----   timeInv
----     ( ((\v ->
----         case v of
----           Nil -> Left Nil
----           Cons a v' -> Right $ (a, v')
----       ) :: (Vec n a) -> Either (Vec n b) (a, Vec (n - 1) a))
----     )


-- TODO(sandy): i think this might not work over time-varying structures
mapFoldVC
    :: forall n a b r
     . (KnownNat n, OkCircuit a, OkCircuit b, OkCircuit r)
    => Circuit (a, r) (b, r)
    -> Circuit (Vec n a, r) (Vec n b, r)
mapFoldVC c = primitive $ Circuit undefined $
  timeInv
    ( ((\(v, r) ->
        case v of
          Nil -> Left (Nil, r)
          Cons a v' -> Right $ ((a, r), v')
      ) :: (Vec n a, r) -> Either (Vec n b, r) ((a, r), Vec (n - 1) a))
    )
  >>> Category.right
        ( Category.first' (c_roar c)
      >>> Category.reassoc'
      >>> Category.second'
          ( Category.swap
        >>> Category.second' Category.copy
        >>> Category.reassoc
        >>> Category.first'
            ((Signal (\a ->
              case unsafeSatisfyGEq1 @(n - 1) of
                Dict -> pumpSignal (c_roar $ mapFoldVC c) a
              ) :: Signal (Vec (n - 1) a, r) (Vec (n - 1) b, r)
            )
        >>> Category.fst'
            )
          )
      >>> Category.reassoc
      >>> Category.first' (timeInv $ uncurry Cons)
        )
  >>> Category.unify

data Dict c where
  Dict :: c => Dict c

unsafeSatisfyGEq1 :: Dict (1 <= n)
unsafeSatisfyGEq1 = unsafeCoerce $ Dict @(1 <= 2)

----   (v, r0) <- f
----   case v of
----     Nil -> pure (Nil, r0)
----     Cons a v_cons -> do
----       (b, r') <- runRoar (c_roar c) _
----       undefined
----       -- let (b, r') = runRoar (c_roar c) (const (a, r0)) t
----       --     (v', _) = runRoar (c_roar $ mapFoldVC c) (const (v_cons, r')) t
----       --   in (Cons b v', r')


zipVC :: Circuit (Vec n a, Vec n b) (Vec n (a, b))
zipVC = primitive $ Circuit undefined $ timeInv $ uncurry V.zip


cloneV :: KnownNat n => Circuit r (Vec n r)
cloneV = primitive $ Circuit undefined $ timeInv V.repeat


fixC :: s -> Circuit (a, s) (b, s) -> Circuit a b
fixC s0 = primitive . Circuit undefined . go s0 . c_roar
  where
    go s k = Signal $ \a ->
      let (k', (b, s')) = pumpSignal k (a, s)
      in (go s' k', b)


foldVC :: Circuit (a, b) b -> Circuit (Vec n a, b) b
foldVC c = primitive $ Circuit undefined $ undefined -- foldSig $ c_roar c

-- foldSig :: Signal (a, b) b -> Signal (Vec n a, b) b
-- foldSig sf@(Signal f) = Signal $ \(v, b) ->
--   case v of
--     Nil -> (foldSig sf, b)
--     Cons a v' ->
--       let (sa, b') = f (a, b)
--           (sv, b'') = pumpSignal (foldSig sf) (v', b')
--        in (_ sa sv, b'')


------------------------------------------------------------------------------
-- | Too slow to run real world physics? JET STREAM IT, BABY.
shortcircuit :: (a -> b) -> Circuit a b -> Circuit a b
shortcircuit f c = Circuit (c_graph c) $ timeInv f

