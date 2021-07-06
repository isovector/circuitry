{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Take2.Product (proj, replace, ProjName) where

import Data.Kind (Type)
import Data.Proxy
import GHC.Generics
import GHC.OverloadedLabels (IsLabel, fromLabel)
import GHC.TypeLits
import Take2.Embed
import Take2.Machinery
import Take2.Primitives (Dict(Dict))
import Unsafe.Coerce (unsafeCoerce)

data ProjName (name  :: Symbol) = ProjName

type family FlattenSels (f :: Type -> Type) :: [Type -> Type] where
  FlattenSels (S1 a b) = '[S1 a b]
  FlattenSels (f :*: g) = Append (FlattenSels f) (FlattenSels g)
  FlattenSels (M1 _1 _2 f) = FlattenSels f

instance (KnownSymbol name, name ~ name') => IsLabel name (ProjName name') where
  fromLabel = ProjName

proj
    :: forall ty name res
     . (GProj (FlattenSels (Rep ty)) ty name res, SeparatePorts ty, KnownSymbol name, SeparatePorts res)
    => ProjName name
    -> Circuit ty res
proj lbl = component ("." <> symbolVal lbl)
         $ gproj @(FlattenSels (Rep ty)) 0 lbl

replace :: forall ty name res. (GProj (FlattenSels (Rep ty)) ty name res, SeparatePorts ty, KnownSymbol name, SeparatePorts res) => ProjName name -> Circuit (res, ty) ty
replace lbl = component ("." <> symbolVal lbl <> "=")
            $ greplace @(FlattenSels (Rep ty)) 0 lbl


type family KnownSize (rep :: Type -> Type) :: Nat where
  KnownSize (M1 _1 _2 f) = KnownSize f
  KnownSize (f :*: g) = KnownSize f + KnownSize g
  KnownSize (K1 _1 a) = SizeOf a


class (Embed ty, Embed res) => GProj (rep :: [Type -> Type]) ty (name :: Symbol) res | ty name rep -> res where
  gproj :: Integer -> ProjName name -> Circuit ty res
  greplace :: Integer -> ProjName name -> Circuit (res, ty) ty


instance {-# OVERLAPPING #-} (Embed res, Embed ty) => GProj (S1 ('MetaSel ('Just name) _1 _2 _3) (K1 _4 res) ': _5) ty name res where
  gproj = gprojImpl
  greplace = greplaceImpl

gprojImpl
    :: forall name res ty
     . (Embed res, Embed ty)
    => Integer
    -> ProjName name
    -> Circuit ty res
gprojImpl n _ =
    withSomeNat n $ \(Proxy :: Proxy n) ->
      case (unsafeProofBigEnough @n  @(SizeOf ty), unsafeProofBigEnough @(SizeOf res) @(SizeOf ty - n)) of
        (Dict, Dict) -> unsafeReinterpret @_ @(Vec n Bool, Vec (SizeOf ty - n) Bool)
                    >>> snd'
                    >>> unsafeReinterpret @_ @(Vec (SizeOf res) Bool, Vec (SizeOf ty - n - SizeOf res) Bool)
                    >>> fst'
                    >>> unsafeParse

greplaceImpl
    :: forall name res ty
     . (Embed res, Embed ty)
    => Integer
    -> ProjName name
    -> Circuit (res, ty) ty
greplaceImpl n _ =
    withSomeNat n $ \(Proxy :: Proxy n) ->
      case (unsafeProofBigEnough @(SizeOf res) @(SizeOf ty - n)) of
        Dict
          -> second' ( unsafeReinterpret @_ @((Vec n Bool, Vec (SizeOf res) Bool), Vec (SizeOf ty - n - SizeOf res) Bool)
                   >>> first' fst'
                     )
         >>> reassoc
         >>> first' swap
         >>> unsafeReinterpret



unsafeProofBigEnough :: forall n m. Dict (n <= m)
unsafeProofBigEnough = unsafeCoerce (Dict @(0 <= 1))

instance (KnownNat (KnownSize f), GProj g ty name res) => GProj (f ': g) ty name res where
  gproj n = gproj @g (n + natVal (Proxy @(KnownSize f)))
  greplace n = greplace @g (n + natVal (Proxy @(KnownSize f)))


