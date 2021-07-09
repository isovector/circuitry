{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}

module Take2.Coproduct where

import           Circuitry.Category
import           Clash.Sized.Vector (Vec (..))
import qualified Clash.Sized.Vector as V
import           Control.Applicative ((<|>))
import           Data.Kind (Type, Constraint)
import           Data.Maybe (fromJust)
import           GHC.Generics
import           GHC.TypeLits
import           GHC.TypeLits.Extra (Max)
import           Take2.Circuit (Circuit, Named (Named))
import           Take2.Embed
import           Take2.Instances
import           Take2.Primitives (Dict(Dict), pad)
import           Unsafe.Coerce (unsafeCoerce)
import GHC.OverloadedLabels

data InjName (name  :: Symbol) where
  InjName :: KnownSymbol name => InjName name

instance (KnownSymbol name', name ~ AppendSymbol "_" name') => IsLabel name (InjName name') where
  fromLabel = InjName

data Tree a = Branch (Tree a) (Tree a) | Leaf a

data Coproduct (xs :: Tree (Symbol, Type)) where
  LHS :: Coproduct ls -> Coproduct ('Branch ls rs)
  RHS :: Coproduct rs -> Coproduct ('Branch ls rs)
  Here :: InjName name -> x -> Coproduct ('Leaf '(name, x))

data Elim (xs :: Tree (Symbol, Type)) (r :: Type) where
  Elim
      :: Embed x
      => InjName name
      -> Circuit x r
      -> Elim ('Leaf '(name, x)) r
  (:+|)
      :: (Embed (Coproduct ls), Embed (Coproduct rs))
      => Elim ls r
      -> Elim rs r -> Elim ('Branch ls rs) r


class GInject (n :: Nat) (rep :: Type -> Type) (name :: Symbol) ty a where
  ginject :: Maybe (Circuit a (Vec n Bool))

instance ( (m + 1) ~ n
         , GInject m f name ty a
         , GInject m g name ty a
         , Embed a
         , KnownNat m
         , KnownNat n
         ) => GInject n (f :+: g) name ty a where
  ginject = fmap (>>> lintro False) (ginject @m @f @name @ty @a)
        <|> fmap (>>> lintro True)  (ginject @m @g @name @ty @a)

instance (SizeOf a <= n, Embed a, KnownNat n) => GInject n (K1 _1 a) name ty a where
  ginject = Just $ serial >>> pad False

instance GInject n f name ty a => GInject n (D1 _1 f) name ty a where
  ginject = ginject @n @f @name @ty @a

instance GInject n f name ty a => GInject n (S1 _1 f) name ty a where
  ginject = ginject @n @f @name @ty @a

instance {-# OVERLAPPING #-} (GInject n f name ty a)
    => GInject n (C1 ('MetaCons name _1 _2) f) name ty a where
  ginject = ginject @n @f @name @ty @a

instance GInject n (C1 ('MetaCons name' _1 _2) f) name ty a where
  ginject = Nothing

lintro :: KnownNat n => Bool -> Circuit (Vec n Bool) (Vec (n + 1) Bool)
lintro b = intro b >>> swap >>> consC

inj
    :: forall x a name
     . (Contains (FlattenCons2 (Rep x)) a, GInject (SizeOf x) (Rep x) name x a, Embed a, Embed x)
    => InjName name
    -> Circuit a x
inj _ = fromJust (ginject @(SizeOf x) @(Rep x) @name @x @a) >>> unsafeParse

type family FlattenCons2 (f :: Type -> Type) :: [Type] where
  FlattenCons2 (K1 a b) = '[b]
  FlattenCons2 U1 = '[()]
  FlattenCons2 (f :+: g) = Append (FlattenCons2 f) (FlattenCons2 g)
  FlattenCons2 (M1 _1 _2 f) = FlattenCons2 f

-- This makes the 'fromJust' in 'inj' safe lol
type family Contains (tys :: [k]) (a :: k) :: Constraint where
  Contains '[] a = TypeError ('Text "Can't inject a " ':<>: 'ShowType a)
  Contains (a ': tys) a = (() :: Constraint)
  Contains (b ': tys) a = Contains tys a


elim
    :: (xs ~ FoldCoprod (Rep a), SizeOf (Coproduct xs) ~ SizeOf a, Embed a, Embed r, Embed (Coproduct xs))
    => Elim xs r
    -> Circuit a r
elim e = serial >>> gelim e >>> unsafeParse


gelim
    :: forall xs r
     . (Embed r, Embed (Coproduct xs))
    => Elim xs r
    -> Circuit (Vec (SizeOf (Coproduct xs)) Bool) (Vec (SizeOf r) Bool)
gelim (Elim name@InjName f) = component (symbolVal name) $ unsafeParse >>> f >>> serial
gelim (ls :+| rs) = coproductBranch ls rs

coproductBranch
    :: forall ls rs r
    . (Embed r, Embed (Coproduct ls), Embed (Coproduct rs))
    => Elim ls r
    -> Elim rs r
    -> Circuit (Vec (SizeOf (Coproduct ('Branch ls rs))) Bool) (Vec (SizeOf r) Bool)
coproductBranch ls rs
    = unconsC
  >>> (unsafeReinterpret >>> component "scrutinize" (scrutinize @(SizeOf (Coproduct ls)) @(SizeOf (Coproduct rs))) >>> unsafeReinterpret)
  >>> first' (gelim ls) *** first' (gelim rs)
  >>> -- component "unify"
      ( both (tribufAll >>> serial)
    >>> unsafeReinterpret @_ @(Vec 2 _)
    >>> pointwiseShort
      )

scrutinize
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Circuit (Named "Tag" Bool, Named "D" (Vec (Max a b) Bool))
               ((Named "DL" (Vec a Bool), Named "L" Bool), (Named "DR" (Vec b Bool), Named "R" Bool))
scrutinize
      = unsafeReinterpret
    >>> swap
    >>> copy
    >>> (second' (notGate >>> copy) >>> reassoc >>> first' (tribufAll >>> separate >>> fst'))
    *** (second' (            copy) >>> reassoc >>> first' (tribufAll >>> separate >>> fst'))
    >>> unsafeReinterpret @((Vec a Bool, Bool), (Vec b Bool, Bool))



type family FoldCoprod2 (f :: Type -> Type) (name :: Symbol) :: (Symbol, Type) where
  FoldCoprod2 (K1 _1 a) name    = '(name, a)
  FoldCoprod2 (M1 _1 _2 f) name = FoldCoprod2 f name


type family FoldCoprod (f :: Type -> Type) :: Tree (Symbol, Type) where
  FoldCoprod (C1 ('MetaCons name _1 _2) f) = 'Leaf (FoldCoprod2 f name)
  -- FoldCoprod U1           = 'Leaf ()
  FoldCoprod (f :+: g)    = 'Branch (FoldCoprod f) (FoldCoprod g)
  FoldCoprod (D1 _1 f) = FoldCoprod f
  FoldCoprod (S1 _1 f) = FoldCoprod f


-- type family Depth (xs :: Tree Type) :: Nat where
--   Depth ('Branch ls rs) = Max (Depth ls) (Depth rs) + 1
--   Depth ('Leaf _) = 0

instance (Embed x, KnownSymbol name) => Embed (Coproduct ('Leaf '(name, x))) where
  type SizeOf (Coproduct ('Leaf '(name, x))) = SizeOf x
  embed (Here _ x) = embed x
  reify v = Here (InjName @name) (reify v)

instance ( KnownNat (SizeOf (Coproduct ls))
         , KnownNat (SizeOf (Coproduct rs))
         , Embed (Coproduct ls)
         , Embed (Coproduct rs)
         , SizeOf (Coproduct ls) <= SizeOf (Coproduct ('Branch ls rs))
         , SizeOf (Coproduct rs) <= SizeOf (Coproduct ('Branch ls rs))
         , 1 <= SizeOf (Coproduct ('Branch ls rs))
         ) => Embed (Coproduct ('Branch ls rs)) where
  type SizeOf (Coproduct ('Branch ls rs)) = Max (SizeOf (Coproduct ls)) (SizeOf (Coproduct rs)) + 1

  {-# INLINE embed #-}
  {-# INLINE reify #-}

  embed (LHS mem) = Cons False $ padV @(SizeOf (Coproduct rs)) $ embed mem
  embed (RHS mem) = Cons True $
    case proofMaxCommutative @(SizeOf (Coproduct rs)) @(SizeOf (Coproduct ls)) of
      Dict -> padV @(SizeOf (Coproduct ls)) $ embed mem

  reify (Cons False v)
    = LHS
    $ reify
    $ V.takeI @_ @(SizeOf (Coproduct ('Branch ls rs)) - 1 - SizeOf (Coproduct ls))
    $ v
  reify (Cons True v)
    = RHS
    $ reify
    $ V.takeI @_ @(SizeOf (Coproduct ('Branch ls rs)) - 1 - SizeOf (Coproduct rs))
    $ v

proofMaxCommutative :: forall n m. Dict (Max m n ~ Max n m)
proofMaxCommutative = unsafeCoerce (Dict @(1 <= 1))


padV :: forall n m. (KnownNat m, KnownNat n) => Vec m Bool -> Vec (Max m n) Bool
padV v = v V.++ V.repeat @(Max m n - m) False
