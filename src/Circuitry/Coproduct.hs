{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}

module Circuitry.Coproduct where

import           Circuitry.Category
import           Clash.Sized.Vector (Vec (..))
import qualified Clash.Sized.Vector as V
import           Control.Applicative ((<|>))
import           Data.Kind (Type, Constraint)
import           Data.Maybe (fromJust)
import           Data.Typeable (Typeable)
import           GHC.Generics
import           GHC.OverloadedLabels
import           GHC.TypeLits
import           GHC.TypeLits.Extra (Max)
import           Prelude hiding (id)
import           Circuitry.Circuit (Circuit, SeparatePorts)
import           Circuitry.Embed hiding (Length)
import           Circuitry.Instances
import           Circuitry.Primitives (Dict(Dict), pad, bypassing)
import           Circuitry.Sing
import           Unsafe.Coerce (unsafeCoerce)


data InjName (name  :: Symbol) where
  InjName :: KnownSymbol name => InjName name

instance (KnownSymbol name', name ~ AppendSymbol "_" name') => IsLabel name (InjName name') where
  fromLabel = InjName

data Tree a = Branch (Tree a) (Tree a) | Leaf a

data Coproduct (xs :: Tree (Symbol, Type)) where
  LHS :: Coproduct ls -> Coproduct ('Branch ls rs)
  RHS :: Coproduct rs -> Coproduct ('Branch ls rs)
  Here :: InjName name -> x -> Coproduct ('Leaf '(name, x))

data ElimList (xs :: [(Symbol, Type)]) b (r :: Type) where
  End :: ElimList '[] b r
  (:+|)
      :: Elim  ('Leaf '(name, x)) b r
      -> ElimList xs b r
      -> ElimList ('(name, x) ': xs) b r

data Elim (xs :: Tree (Symbol, Type)) b (r :: Type) where
  (:->)
      :: (Embed x, Typeable x)
      => InjName name
      -> Circuit (x, b) r
      -> Elim ('Leaf '(name, x)) b r
  (:~>)
      :: InjName name
      -> Circuit b r
      -> Elim ('Leaf '(name, ())) b r
  (:=~>)
      :: InjName name
      -> Circuit () r
      -> Elim ('Leaf '(name, ())) () r
  (:=>)
      :: (Embed x, Typeable x)
      => InjName name
      -> Circuit x r
      -> Elim ('Leaf '(name, x)) () r
  Both
      :: (Embed (Coproduct ls), Embed (Coproduct rs))
      => Elim ls b r
      -> Elim rs b r -> Elim ('Branch ls rs) b r

infix 2 :->
infix 2 :=>
infix 2 :~>
infix 2 :=~>
infixr 1 :+|


elim2SplitAt
    :: (SplitAt (Div (Length xs) 2) xs ~ '(ys, zs))
    => ElimList xs b r
    -> (ElimList ys b r, ElimList zs b r)
elim2SplitAt es =
  let xs = unsafeCoerce @_ @[_] es
      (l, r) = splitAt (length xs `div` 2) xs
   in  (unsafeCoerce l, unsafeCoerce r)


class FoldElim xs b r where
  foldElim :: ElimList xs b r -> Elim (FoldBal 'Branch (MapT 'Leaf xs)) b r

instance {-# OVERLAPPING #-} FoldElim '[ '(name, x) ] b r where
  foldElim (e :+| End) = e

instance ( ls ~ (Take (Div (Length xs) 2) xs)
         , rs ~ (Drop (Div (Length xs) 2) xs)
         , fls ~ (Fold_Bal 'Branch (Length (MapT 'Leaf ls)) (MapT 'Leaf ls))
         , frs ~ (Fold_Bal 'Branch (Length (MapT 'Leaf rs)) (MapT 'Leaf rs))
         , Fold_Bal 'Branch (Length (MapT 'Leaf xs)) (MapT 'Leaf xs)
         ~ 'Branch fls frs
         , FoldElim ls b r
         , FoldElim rs b r
         , Embed (Coproduct fls)
         , Embed (Coproduct frs)
         )
    => FoldElim xs b r where
  foldElim xs =
    let (l,r) = elim2SplitAt xs
    in foldElim l `Both` foldElim r



class GInjectThread (n :: Nat) (rep :: Type -> Type) (name :: Symbol) ty a where
  ginjectThread :: Maybe (Circuit a (Vec n Bool))

class GInject (n :: Nat) (rep :: Type -> Type) ty a where
  ginject :: Circuit a (Vec n Bool)

instance (Embed a, KnownNat n, SizeOf a <= n) => GInject n (K1 _1 a) ty a where
  ginject = serial >>> pad False

instance GInject n f ty a => GInject n (S1 _1 f) ty a where
  ginject = ginject @n @f @ty @a

instance ( SizeOf a + SizeOf b <= n
         , GInject (SizeOf a) f a a
         , GInject (SizeOf b) g b b
         , Embed a
         , Embed b
         , KnownNat n
         ) => GInject n (f :*: g) ty (a, b) where
  ginject = ginject @(SizeOf a) @f @a @a
        *** ginject @(SizeOf b) @g @b @b
        >>> serial
        >>> pad False

instance ( GInjectThread (n - 1) f name ty a
         , GInjectThread (n - 1) g name ty a
         , 1 <= n
         , Embed a
         , KnownNat n
         ) => GInjectThread n (f :+: g) name ty a where
  ginjectThread = fmap (>>> lintro False) (ginjectThread @(n - 1) @f @name @ty @a)
              <|> fmap (>>> lintro True)  (ginjectThread @(n - 1) @g @name @ty @a)

instance (GInject n (K1 _1 a) ty a) => GInjectThread n (K1 _1 a) name ty a where
  ginjectThread = Just $ ginject @n @(K1 _1 a) @ty @a

instance (GInject n (f :*: g) ty a) => GInjectThread n (f :*: g) name ty a where
  ginjectThread = Just $ ginject @n @(f :*: g) @ty @a

instance GInjectThread n f name ty a => GInjectThread n (D1 _1 f) name ty a where
  ginjectThread = ginjectThread @n @f @name @ty @a

instance GInjectThread n f name ty a => GInjectThread n (S1 _1 f) name ty a where
  ginjectThread = ginjectThread @n @f @name @ty @a

instance {-# OVERLAPPING #-} (GInjectThread n f name ty a)
    => GInjectThread n (C1 ('MetaCons name _1 _2) f) name ty a where
  ginjectThread = ginjectThread @n @f @name @ty @a

instance GInjectThread n (C1 ('MetaCons name' _1 _2) f) name ty a where
  ginjectThread = Nothing

lintro :: KnownNat n => Bool -> Circuit (Vec n Bool) (Vec (n + 1) Bool)
lintro b = intro b >>> swap >>> consC

type Inj x a name
     = ( Contains (FlattenCons2 (Rep x)) a
       , GInjectThread (SizeOf x) (Rep x) name x a
       , Embed a
       , Embed x
       )

inj
    :: forall x a name
     . Inj x a name
    => InjName name
    -> Circuit a x
inj _ = fromJust (ginjectThread @(SizeOf x) @(Rep x) @name @x @a) >>> unsafeParse

type family FlattenCons2 (f :: Type -> Type) :: [Type] where
  FlattenCons2 (K1 a b) = '[b]
  FlattenCons2 U1 = '[()]
  FlattenCons2 (f :+: g) = Append (FlattenCons2 f) (FlattenCons2 g)
  FlattenCons2 (f :*: g) = '[FoldCoprod2 (f :*: g)]
  FlattenCons2 (M1 _1 _2 f) = FlattenCons2 f

-- This makes the 'fromJust' in 'inj' safe lol
type family Contains (tys :: [k]) (a :: k) :: Constraint where
  Contains '[] a = TypeError ('Text "Can't inject a " ':<>: 'ShowType a)
  Contains (a ': tys) a = (() :: Constraint)
  Contains (b ': tys) a = Contains tys a


elim
    :: ( xs ~ FoldCoprod (Rep a)
       , SizeOf (Coproduct xs) ~ SizeOf a
       , Embed a
       , Embed r
       , Embed (Coproduct xs)
       , Embed b
       , SeparatePorts b
       )
    => Elim xs b r
    -> Circuit (a, b) r
elim e = first' serial >>> gelim e >>> unsafeParse

elim_
    :: ( xs ~ FoldCoprod (Rep a)
       , SizeOf (Coproduct xs) ~ SizeOf a
       , Embed a
       , Embed r
       , Embed (Coproduct xs)
       )
    => Elim xs () r
    -> Circuit a r
elim_ e = serial >>> create >>> gelim e >>> unsafeParse


gelim
    :: forall xs b r
     . (Embed r, Embed (Coproduct xs), KnownNat (SizeOf b), Embed b, SeparatePorts b)
    => Elim xs b r
    -> Circuit (BitsOf (Coproduct xs), b) (BitsOf r)
gelim (name@InjName :-> f) = bypassing $ component (symbolVal name) (first' unsafeParse) >>> f >>> serial
gelim (name@InjName :=> f) = bypassing $ component (symbolVal name) (first' unsafeParse) >>> fst' >>> f >>> serial
gelim (name@InjName :~> f) = bypassing $ component (symbolVal name) snd' >>> f >>> serial
gelim (name@InjName :=~> f) = bypassing $ component (symbolVal name) (first' unsafeParse) >>> fst' >>> f >>> serial
gelim (Both ls rs) = bypassing $ coproductBranch ls rs

coproductBranch
    :: forall ls rs b r
    . (Embed r, Embed (Coproduct ls), Embed (Coproduct rs), Embed b, SeparatePorts b)
    => Elim ls b r
    -> Elim rs b r
    -> Circuit (BitsOf (Coproduct ('Branch ls rs)), b) (BitsOf r)
coproductBranch ls rs
    = first' (unconsC >>> component "scrutinize" (scrutinize @(SizeOf (Coproduct ls)) @(SizeOf (Coproduct rs))))
  >>> swap
  >>> distribP
  -- TODO(sandy): THIS DOESNT TRIBUF BEFORE ELIMINATING
  >>> (reassoc >>> first' (swap >>> gelim ls))
  *** (reassoc >>> first' (swap >>> gelim rs))
  >>> -- component "unify"
      ( (tribufAll >>> serial)
    *** (tribufAll >>> serial)
    >>> pairwiseShort
      )

scrutinize
    :: forall a r
     . (KnownNat a, KnownNat r)
    => Circuit (Bool, Vec (Max a r) Bool)
               ((Vec a Bool, Bool), (Vec r Bool, Bool))
scrutinize
      = bypassing
      $ swap
    >>> copy
    >>> (second' (notGate >>> copy) >>> reassoc >>> first' (tribufAll >>> separate >>> fst'))
    *** (second' (            copy) >>> reassoc >>> first' (tribufAll >>> separate >>> fst'))


type family FoldCoprod2 (f :: Type -> Type) :: Type where
  FoldCoprod2 (K1 _1 a)    = a
  FoldCoprod2 U1           = ()
  FoldCoprod2 (f :*: g)    = (FoldCoprod2 f, FoldCoprod2 g)
  FoldCoprod2 (M1 _1 _2 f) = FoldCoprod2 f


type family FoldCoprod (f :: Type -> Type) :: Tree (Symbol, Type) where
  FoldCoprod (C1 ('MetaCons name _1 _2) f) = 'Leaf ( '(name, FoldCoprod2 f))
  -- FoldCoprod U1           = 'Leaf ()
  FoldCoprod (f :+: g)    = 'Branch (FoldCoprod f) (FoldCoprod g)
  FoldCoprod (D1 _1 f) = FoldCoprod f
  FoldCoprod (S1 _1 f) = FoldCoprod f


instance (Embed x, KnownSymbol name) => Embed (Coproduct ('Leaf '(name, x))) where
  type SizeOf (Coproduct ('Leaf '(name, x))) = SizeOf x
  embed (Here _ x) = embed x
  reify v = Here (InjName @name) (reify v)


instance ( KnownNat (SizeOf (Coproduct ls))
         , KnownNat (SizeOf (Coproduct rs))
         , Embed (Coproduct ls)
         , Embed (Coproduct rs)
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
  reify _ = error "impossible"

proofMaxCommutative :: forall n m. Dict (Max m n ~ Max n m)
proofMaxCommutative = unsafeCoerce (Dict @(1 <= 1))


padV :: forall n m. (KnownNat m, KnownNat n) => Vec m Bool -> Vec (Max m n) Bool
padV v = v V.++ V.repeat @(Max m n - m) False

