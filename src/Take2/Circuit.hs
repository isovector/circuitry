{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Circuit where

import           Circuitry.Catalyst (Roar(..), loop, Time)
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
import           Prelude hiding ((.), id, sum)
import           Take2.Embed
import           Take2.Graph
import           Test.QuickCheck
import           Unsafe.Coerce (unsafeCoerce)

data Circuit a b = Circuit
  { c_graph :: Graph a b
  , c_roar :: Roar Time a b
  }

class (Stuff a, Embed a) => OkCircuit a
instance (Stuff a, Embed a) => OkCircuit a

instance Category Circuit where
  type Ok Circuit = OkCircuit
  id = Circuit id id
  Circuit gg gr . Circuit fg fr = Circuit (gg . fg) (gr . fr)

instance SymmetricProduct Circuit where
  swap :: forall a b. (OkCircuit a, OkCircuit b) => Circuit (a, b) (b, a)
  swap =
    primitive $ raw $ Circuit (genComp "swap") $ timeInv $ \v ->
      let (va, vb) = V.splitAtI @(SizeOf a) v
      in vb V.++ va

  reassoc = unsafeReinterpret

instance MonoidalProduct Circuit where
  first' c =
    primitive $ raw $ Circuit (genComp "first'") $ Roar $ \f t ->
      let v = f t
          (va, vc) = V.splitAtI v
          b = runRoar (c_roar c) (const $ reify va) t
      in embed b V.++ vc
  second' c = swap >>> first' c >>> swap

instance Cartesian Circuit where
  consume = primitive $ raw $ Circuit (genComp "consume") $ timeInv $ const Nil
  copy = primitive $ raw $ Circuit (genComp "copy") $ timeInv $ \v -> v V.++ v
  fst' = primitive $ raw $ Circuit (genComp "fst") $ timeInv V.takeI
  snd' = primitive $ raw $ Circuit (genComp "snd") $ timeInv V.dropI

instance MonoidalSum Circuit where
  (+++) l r = eitherE (l >>> injl) (r >>> injr)
  left = flip (+++) id
  right = (+++) id

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


unsafeReinterpret :: (OkCircuit a, OkCircuit b, SizeOf a ~ SizeOf b) => Circuit a b
unsafeReinterpret = raw id


raw :: (OkCircuit a, OkCircuit b) => Circuit (Vec (SizeOf a) Bool) (Vec (SizeOf b) Bool) -> Circuit a b
raw c = Circuit (genComp "unravel" >>> c_graph c >>> genComp "ravel") $
  Roar $ \f t ->
    let x = runRoar (c_roar c) (fmap embed f)
     in reify $ x t


primitive :: Circuit a b -> Circuit a b
primitive = id


timeInv :: (a -> b) -> Roar r a b
timeInv fab = Roar (\ fra -> fab . fra)


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


create :: OkCircuit a => Circuit a (a, ())
create = unsafeReinterpret


destroy :: OkCircuit a => Circuit (a, ()) a
destroy = fst'


constC :: a -> Circuit () a
constC a = primitive $ Circuit undefined $ timeInv $ const a


serial :: OkCircuit a => Circuit a (Vec (SizeOf a) Bool)
serial = unsafeReinterpret


unsafeParse :: OkCircuit a => Circuit (Vec (SizeOf a) Bool) a
unsafeParse = unsafeReinterpret


pad
    :: forall m n a
     . (KnownNat m, KnownNat n, m <= n)
    => a
    -> Circuit (Vec m a) (Vec n a)
pad a = primitive $ Circuit undefined $ timeInv $ \v -> V.repeat @(n - m) a V.++ v


consC :: (KnownNat n, OkCircuit a) => Circuit (a, Vec n a) (Vec (n + 1) a)
consC = unsafeReinterpret


unconsC :: (KnownNat n, OkCircuit a) => Circuit (Vec (n + 1) a) (a, Vec n a)
unconsC = unsafeReinterpret


separate :: (KnownNat m, KnownNat n, m <= n, OkCircuit a) => Circuit (Vec n a) (Vec m a, Vec (n - m) a)
separate = unsafeReinterpret


unseparate :: (KnownNat m, KnownNat n, m <= n, OkCircuit a) => Circuit (Vec m a, Vec (n - m) a) (Vec n a)
unseparate = unsafeReinterpret


reassoc' :: forall a b c. (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit ((a, b), c) (a, (b, c))
reassoc' = unsafeReinterpret


ifC :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit a b -> Circuit (Bool, a) b
ifC t f = second' (copy >>> (t *** f))
      >>> distrib
      >>> second' (first' notGate)
      >>> both (second' serial >>> distribV >>> mapV andGate)
      >>> zipVC
      >>> mapV orGate
      >>> unsafeParse


distrib :: (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit (a, (b, c)) ((a, b), (a, c))
distrib = first' copy
      >>> reassoc'
      >>> second' ( swap
                >>> reassoc'
                >>> second' swap
                  )
      >>> reassoc


nandGate :: Circuit (Bool, Bool) Bool
nandGate = primitive $ Circuit (genComp "nand") $ timeInv $ not . uncurry (&&)


notGate :: Circuit Bool Bool
notGate = copy >>> nandGate


andGate :: Circuit (Bool, Bool) Bool
andGate = nandGate >>> notGate


orGate :: Circuit (Bool, Bool) Bool
orGate = both notGate >>> nandGate


xorGate :: Circuit (Bool, Bool) Bool
xorGate = copy >>> (second' notGate >>> andGate) *** (first' notGate >>> andGate) >>> orGate


both :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit (a, a) (b, b)
both f = f *** f


mapV
    :: (KnownNat n, OkCircuit a, OkCircuit b)
    => Circuit a b
    -> Circuit (Vec n a) (Vec n b)
mapV c = create >>> mapFoldVC (destroy >>> c >>> create) >>> destroy


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


distribV :: (OkCircuit a, OkCircuit b, KnownNat n) => Circuit (a, Vec n b) (Vec n (a, b))
distribV = first' cloneV >>> zipVC


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


------------------------------------------------------------------------------
-- | Too slow to run real world physics? JET STREAM IT, BABY.
shortcircuit :: (a -> b) -> Circuit a b -> Circuit a b
shortcircuit f c = Circuit (c_graph c) $ Roar $ \fa t -> f (fa t)

