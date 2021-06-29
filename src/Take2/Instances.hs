{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Instances where

import           Circuitry.Catalyst (Roar(..))
import           Circuitry.Category (Category(..), (>>>), swapE, SymmetricProduct (reassoc), MonoidalProduct (second'), Cartesian(..), SymmetricSum(..), MonoidalSum)
import           Circuitry.Category (MonoidalProduct(..))
import           Circuitry.Category (MonoidalSum(..))
import           Circuitry.Category (SymmetricProduct(..))
import           Clash.Sized.Vector (Vec(..))
import           Data.Generics.Labels ()
import           GHC.TypeLits
import           Prelude hiding ((.), id, sum)
import           Take2.Circuit
import           Take2.Embed
import qualified Take2.Primitives as Prim


instance SymmetricProduct Circuit where
  swap = Prim.swap
  reassoc = unsafeReinterpret

instance MonoidalProduct Circuit where
  first' = Prim.first'
  second' c = swap >>> first' c >>> swap

instance Cartesian Circuit where
  consume = Prim.consume
  copy = Prim.copy
  fst' = Prim.fst'
  snd' = swap >>> fst'

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
unsafeReinterpret = Prim.raw id

raise :: OkCircuit a => Circuit a (Vec 1 a)
raise = unsafeReinterpret

lower :: OkCircuit a => Circuit (Vec 1 a) a
lower = unsafeReinterpret


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
   >>> (Prim.constC False *** (serial >>> Prim.pad False))
   >>> consC
   >>> unsafeParse


injr :: (OkCircuit a, OkCircuit b) => Circuit a (Either b a)
injr = injl >>> swapE


create :: OkCircuit a => Circuit a (a, ())
create = unsafeReinterpret


destroy :: OkCircuit a => Circuit (a, ()) a
destroy = fst'


serial :: OkCircuit a => Circuit a (Vec (SizeOf a) Bool)
serial = unsafeReinterpret


unsafeParse :: OkCircuit a => Circuit (Vec (SizeOf a) Bool) a
unsafeParse = unsafeReinterpret


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
      >>> Prim.zipVC
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


notGate :: Circuit Bool Bool
notGate = copy >>> Prim.nandGate


andGate :: Circuit (Bool, Bool) Bool
andGate = Prim.nandGate >>> notGate


orGate :: Circuit (Bool, Bool) Bool
orGate = both notGate >>> Prim.nandGate


xorGate :: Circuit (Bool, Bool) Bool
xorGate = copy >>> (second' notGate >>> andGate) *** (first' notGate >>> andGate) >>> orGate


both :: (OkCircuit a, OkCircuit b) => Circuit a b -> Circuit (a, a) (b, b)
both f = f *** f


mapV
    :: (KnownNat n, OkCircuit a, OkCircuit b)
    => Circuit a b
    -> Circuit (Vec n a) (Vec n b)
mapV c = create >>> Prim.mapFoldVC (destroy >>> c >>> create) >>> destroy


distribV :: (OkCircuit a, OkCircuit b, KnownNat n) => Circuit (a, Vec n b) (Vec n (a, b))
distribV = first' Prim.cloneV >>> Prim.zipVC

