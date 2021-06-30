{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

module Take2.Instances where

import           Circuitry.Catalyst (Roar(..), Time)
import           Circuitry.Category (Category(..), (>>>), swapE, SymmetricProduct (reassoc), MonoidalProduct (second'), Cartesian(..), SymmetricSum(..), MonoidalSum, Distrib (distrib), factor)
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
import Test.QuickCheck
import qualified Data.Bits as B
import Unsafe.Coerce (unsafeCoerce)


instance Arbitrary (Roar Time a b) => Arbitrary (Circuit a b) where
  arbitrary = Circuit <$> pure (error "yo") <*> arbitrary

instance SymmetricProduct Circuit where
  swap = Prim.swap
  reassoc = unsafeReinterpret
  reassoc' = unsafeReinterpret

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
  distrib = distribE
  factor = undefined

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


{-# RULES
"unsafeReinterpret . unsafeReinterpret" unsafeReinterpret . unsafeReinterpret = unsafeReinterpret
#-}


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
destroy = unsafeReinterpret


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


distribP :: (OkCircuit a, OkCircuit b, OkCircuit c) => Circuit (a, (b, c)) ((a, b), (a, c))
distribP = first' copy
      >>> reassoc'
      >>> second' ( swap
                >>> reassoc'
                >>> second' swap
                  )
      >>> reassoc


notGate :: Circuit Bool Bool
notGate = copy >>> Prim.nandGate


andGate :: Circuit (Bool, Bool) Bool
andGate = Prim.shortcircuit (uncurry (&&))
         $ Prim.nandGate >>> notGate


orGate :: Circuit (Bool, Bool) Bool
orGate = Prim.shortcircuit (uncurry (||))
       $ both notGate >>> Prim.nandGate

norGate :: Circuit (Bool, Bool) Bool
norGate = orGate >>> notGate


xorGate :: Circuit (Bool, Bool) Bool
xorGate = Prim.shortcircuit (uncurry B.xor)
        $ copy >>> (second' notGate >>> andGate) *** (first' notGate >>> andGate) >>> orGate


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

veryUnsafeCoerce :: forall a b. Circuit a b
veryUnsafeCoerce = Circuit undefined $ unsafeCoerce $ Roar id

-- mapFoldVC
--     :: forall n a b r
--      . (KnownNat n, OkCircuit a, OkCircuit b, OkCircuit r)
--     => Circuit (a, r) (b, r)
--     -> Circuit (Vec n a, r) (Vec n b, r)
-- mapFoldVC c = first' ((
--                 case Prim.unsafeSatisfyGEq1 @(n - 1) of
--                   Prim.Dict -> (Prim.induction @n :: Circuit (Vec n a) (Either (Vec 0 a) (a, Vec (n - 1) a)))
--                      ) )
--           >>> swap
--           >>> distrib
--           >>> (swap >>> veryUnsafeCoerce)
--           +++ ( reassoc
--             >>> first' (swap >>> c)
--             >>> reassoc'
--             >>> second'
--                 ( swap
--               >>> second' copy
--               >>> reassoc
--               >>> first' (mapFoldVC c)
--               >>> fst'
--                 )
--             >>> reassoc
--             >>> first' consC
--               )
--           >>> deject


distribE
    :: (OkCircuit a, OkCircuit b, OkCircuit c)
    => Circuit (a, Either b c) (Either (a, b) (a, c))
distribE = second' (serial >>> unconsC) >>> reassoc >>> first' swap >>> veryUnsafeCoerce

