{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}

module Take2.Coproduct where

import           Circuitry.Category
import           Clash.Sized.Vector (Vec (..))
import qualified Clash.Sized.Vector as V
import           Data.Kind (Type)
import           GHC.Generics
import           GHC.TypeLits
import           GHC.TypeLits.Extra (Max)
import           Take2.Circuit (Circuit)
import           Take2.Embed
import           Take2.Instances
import           Take2.Primitives (Dict(Dict), zipVC)
import           Unsafe.Coerce (unsafeCoerce)

data Tree a = Branch (Tree a) (Tree a) | Leaf a

data Coproduct (xs :: Tree Type) where
  LHS :: Coproduct ls -> Coproduct ('Branch ls rs)
  RHS :: Coproduct rs -> Coproduct ('Branch ls rs)
  Here :: x -> Coproduct ('Leaf x)

data Elim (xs :: Tree Type) (r :: Type) where
  Elim :: Embed x => Circuit x r -> Elim ('Leaf x) r
  (:+|)
      :: (Embed (Coproduct ls), Embed (Coproduct rs))
      => Elim ls r
      -> Elim rs r -> Elim ('Branch ls rs) r


-- test :: Circuit (Either Bool Word4) Bool
-- test = elim $ Elim (notGate >>> notGate >>> notGate)
--           :+| Elim (serial >>> unconsC >>> fst')


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
gelim (Elim f) = unsafeParse >>> f >>> serial
gelim (ls :+| rs) = coproductBranch ls rs

coproductBranch
    :: forall ls rs r
    . (Embed r, Embed (Coproduct ls), Embed (Coproduct rs))
    => Elim ls r
    -> Elim rs r
    -> Circuit (Vec (SizeOf (Coproduct ('Branch ls rs))) Bool) (Vec (SizeOf r) Bool)
coproductBranch ls rs
    = unconsC
  >>> swap
  >>> copy
  >>> (second' (notGate >>> copy) >>> reassoc >>> first' (tribufAll >>> separate >>> fst' >>> gelim ls) >>> tribufAll)
  *** (second' (            copy) >>> reassoc >>> first' (tribufAll >>> separate >>> fst' >>> gelim rs) >>> tribufAll)
  >>> both serial
  -- >>> zipVC
  -- >>> mapV orGate
  >>> unsafeReinterpret @_ @(Vec 2 _)
  >>> pointwiseShort


type family FoldCoprod (f :: Type -> Type) :: Tree Type where
  FoldCoprod (K1 _1 a)    = 'Leaf a
  FoldCoprod U1           = 'Leaf ()
  FoldCoprod (f :+: g)    = 'Branch (FoldCoprod f) (FoldCoprod g)
  FoldCoprod (M1 _1 _2 f) = FoldCoprod f


-- type family Depth (xs :: Tree Type) :: Nat where
--   Depth ('Branch ls rs) = Max (Depth ls) (Depth rs) + 1
--   Depth ('Leaf _) = 0

instance (Embed x) => Embed (Coproduct ('Leaf x)) where
  type SizeOf (Coproduct ('Leaf x)) = SizeOf x
  embed (Here x) = embed x
  reify v = Here (reify v)

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

