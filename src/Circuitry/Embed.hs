{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module Circuitry.Embed
  ( module Circuitry.Embed
  , Identity(..)
  ) where

import           Circuitry.Category (Category(..))
import           Circuitry.Word
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable hiding (sum)
import           Data.Functor.Identity
import           Data.Generics.Labels ()
import           Data.Kind (Type)
import           Data.Maybe (fromMaybe)
import           Data.Typeable
import           Data.Word (Word8, Word64, Word32, Word16)
import           GHC.Generics
import           GHC.TypeLits
import           GHC.TypeLits.Extra
import           Prelude hiding ((.), id, sum)
import           Test.QuickCheck (Arbitrary(..), oneof)

deriving anyclass instance Embed a => Embed (Identity a)

type BitsOf a = Vec (SizeOf a) Bool


class KnownNat (SizeOf a) => Embed (a :: Type) where
  type SizeOf a :: Nat
  type SizeOf a = GSizeOf (Rep a)

class Embed a => Reify a where
  embed :: a -> BitsOf a
  default embed :: (SizeOf a ~ GSizeOf (Rep a), GReify (Rep a), Generic a) => a -> BitsOf a
  embed = gembed . from
  reify :: BitsOf a -> a
  default reify :: (SizeOf a ~ GSizeOf (Rep a), GReify (Rep a), Generic a) => BitsOf a -> a
  reify = to . greify

{-# RULES
"embed . reify" forall a. embed (reify a) = a
"reify . embed" forall a. reify (embed a) = a
"gembed . greify" forall a. gembed (greify a) = a
"greify . gembed" forall a. greify (gembed a) = a
#-}


class KnownNat (GSizeOf f) => GEmbed (f :: Type -> Type) where
  type GSizeOf f :: Nat

class KnownNat (GSizeOf f) => GReify f where
  gembed :: f x -> Vec (GSizeOf f) Bool
  greify :: Vec (GSizeOf f) Bool -> f x

instance GEmbed f => GEmbed (M1 _1 _2 f) where
  type GSizeOf (M1 _1 _2 f) = GSizeOf f

instance GReify f => GReify (M1 _1 _2 f) where
  gembed = gembed . unM1
  greify = M1 . greify
  {-# INLINABLE[~2] gembed #-}
  {-# INLINABLE[~2] greify #-}

instance GEmbed U1 where
  type GSizeOf U1 = 0

instance GReify U1 where
  gembed U1 = Nil
  greify _ = U1
  {-# INLINABLE[~2] gembed #-}
  {-# INLINABLE[~2] greify #-}

instance Embed a => GEmbed (K1 _1 a) where
  type GSizeOf (K1 _1 a) = SizeOf a

instance Reify a => GReify (K1 _1 a) where
  gembed = embed . unK1
  greify = K1 . reify
  {-# INLINABLE[~2] gembed #-}
  {-# INLINABLE[~2] greify #-}

instance (GEmbed f, GEmbed g) => GEmbed (f :*: g) where
  type GSizeOf (f :*: g) = GSizeOf f + GSizeOf g

instance (GReify f, GReify g) => GReify (f :*: g) where
  gembed (f :*: g) = gembed f V.++ gembed g
  greify v =
    let (a, b) = V.splitAtI v
     in greify a :*: greify b
  {-# INLINABLE[~2] gembed #-}
  {-# INLINABLE[~2] greify #-}

instance (GEmbed f, GEmbed g) => GEmbed (f :+: g) where
  type GSizeOf (f :+: g) = Max (GSizeOf f) (GSizeOf g) + 1

instance (GReify f, GReify g) => GReify (f :+: g) where
  gembed (L1 f) =
    case maxProof' @(GSizeOf f) @(GSizeOf g) of
      MaxProof -> False :> (gembed f V.++ V.repeat False)
  gembed (R1 g) =
    case maxProof' @(GSizeOf f) @(GSizeOf g) of
      MaxProof -> True :> (gembed g V.++ V.repeat False)
  greify (t :> v) =
    case maxProof' @(GSizeOf f) @(GSizeOf g) of
      MaxProof ->
        case t of
          False -> L1 $ greify $ V.takeI v
          True  -> R1 $ greify $ V.takeI v
  greify _ = error "impossible"
  {-# INLINABLE[~2] gembed #-}
  {-# INLINABLE[~2] greify #-}


instance Embed ()
instance Reify ()

instance Embed a => Embed (Maybe a)
instance Reify a => Reify (Maybe a)


embedWord :: (B.Bits a, KnownNat m) => a -> Vec m Bool
embedWord w =
  fromMaybe (error "embedWord: faulty Bits instance") $ V.fromList $
    fmap (B.testBit w) [0 .. B.bitSize w - 1]
{-# INLINABLE[~2] embedWord #-}

reifyWord :: (B.Bits a, KnownNat m, Num a) => Vec m Bool -> a
reifyWord w =
  let s b = B.shiftL (bool 0 1 b)
   in foldr @[] (B..|.) 0 $ zipWith s (V.toList w) [0..]
{-# INLINABLE[~2] reifyWord #-}


instance Embed Word2 where
  type SizeOf Word2 = 2

instance Reify Word2 where
  embed = embedWord
  reify = reifyWord

instance Embed Word3 where
  type SizeOf Word3 = 3

instance Reify Word3 where
  embed = embedWord
  reify = reifyWord

instance Embed Word4 where
  type SizeOf Word4 = 4

instance Reify Word4 where
  embed = embedWord
  reify = reifyWord

instance Embed Word8 where
  type SizeOf Word8 = 8

instance Reify Word8 where
  embed = embedWord
  reify = reifyWord

instance Embed Word16 where
  type SizeOf Word16 = 16

instance Reify Word16 where
  embed = embedWord
  reify = reifyWord

instance Embed Word32 where
  type SizeOf Word32 = 32

instance Reify Word32 where
  embed = embedWord
  reify = reifyWord

instance Embed Word64 where
  type SizeOf Word64 = 64

instance Reify Word64 where
  embed = embedWord
  reify = reifyWord

instance Embed Bool
instance Reify Bool

instance (Embed a, Embed b) => Embed (a, b)
instance (Reify a, Reify b) => Reify (a, b)

instance (Embed a, KnownNat n) => Embed (Vec n a) where
  type SizeOf (Vec n a) = n * SizeOf a

instance (Reify a, KnownNat n) => Reify (Vec n a) where
  embed = V.concatMap embed
  reify = V.map reify . V.unconcatI

instance (Embed a, Embed b) => Embed (Either a b)
instance (Reify a, Reify b) => Reify (Either a b)


data MaxProof a b where
  MaxProof :: (KnownNat na, KnownNat nb, Max a b ~ (a + na), Max a b ~ (b + nb)) => MaxProof a b

maxProof :: (KnownNat (SizeOf a), KnownNat (SizeOf b)) => MaxProof (SizeOf a) (SizeOf b)
maxProof = maxProof'

maxProof' :: forall a b. (KnownNat a, KnownNat b) => MaxProof a b
maxProof' =
  let a = natVal $ Proxy @a
      b = natVal $ Proxy @b
      m = max a b
      na = m - a
      nb = m - b
   in withSomeNat na $ \(_ :: Proxy na) ->
      withSomeNat nb $ \(_ :: Proxy nb) ->
        case sameNat (Proxy @(Max a b)) (Proxy @(a + na)) of
          Just Refl ->
            case sameNat (Proxy @(Max a b)) (Proxy @(b + nb)) of
              Just Refl -> MaxProof
              Nothing -> error "impossible failure to synthesize MaxProof"
          Nothing -> error "impossible failure to synthesize MaxProof"


withSomeNat :: Integer -> (forall n. KnownNat n => Proxy n -> r) -> r
withSomeNat i f =
  case someNatVal i of
   Nothing -> error "don't be an idiot"
   Just (SomeNat n) -> f n
{-# INLINABLE withSomeNat #-}


data HList (ts :: [Type]) where
  HNil :: HList '[]
  (:>>)
      :: a
      -> HList ts
      -> HList (a ': ts)

infixr 5 :>>

instance Embed (HList '[]) where
  type SizeOf (HList '[]) = 0

instance Reify (HList '[]) where
  embed HNil = Nil
  reify _ = HNil

instance (Embed (HList ts), Embed a) => Embed (HList (a ': ts)) where
  type SizeOf (HList (a ': ts)) = SizeOf a + SizeOf (HList ts)

instance (Reify (HList ts), Reify a) => Reify (HList (a ': ts)) where
  embed (vec :>> jv') = embed vec V.++ embed jv'
  reify vs =
    let (here, there) = V.splitAtI vs
     in reify here :>> reify there


type family Append (xs :: [k]) (ys :: [k]) :: [k] where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

type family FlattenCons (f :: Type -> Type) :: [Type -> Type] where
  FlattenCons (K1 a b) = TypeError ('Text "K1? in my flatten cons? It's likier than you think")
  FlattenCons (C1 a b) = '[S1 a b]
  FlattenCons (f :+: g) = Append (FlattenCons f) (FlattenCons g)
  FlattenCons (M1 _1 _2 f) = FlattenCons f

type family Length (ts :: [k]) :: Nat where
  Length '[] = 0
  Length (a ': as) = 1 + Length as

newtype EmbededEnum a = EmbededEnum a
  deriving newtype (Enum, Bounded)
  deriving stock Generic

instance (Enum a, Bounded a) => Arbitrary (EmbededEnum a) where
  arbitrary = oneof $ fmap pure $ enumFromTo minBound maxBound

type EnumBitSize t = EnumBitSizeImpl1 (Length (FlattenCons (Rep t)))

type EnumBitSizeImpl1 len = EnumBitSizeImpl (len <=? 2) len

type family EnumBitSizeImpl (b :: Bool) (len :: Nat) where
  EnumBitSizeImpl 'True len = len - 1
  EnumBitSizeImpl 'False len = (Min (Log2 len) (Log2 (len - 1))) + 1

instance ( Enum a
         , Bounded a
         , Generic a
         , KnownNat (EnumBitSizeImpl (Length (FlattenCons (Rep a)) <=? 2) (Length (FlattenCons (Rep a))))
         , SizeOf (EmbededEnum a) <= 8
         ) => Embed (EmbededEnum a) where
  type SizeOf (EmbededEnum a) = EnumBitSize a

instance ( Enum a
         , Bounded a
         , Generic a
         , KnownNat (EnumBitSizeImpl (Length (FlattenCons (Rep a)) <=? 2) (Length (FlattenCons (Rep a))))
         , SizeOf (EmbededEnum a) <= 8
         ) => Reify (EmbededEnum a) where
  embed
    = V.takeI @(SizeOf (EmbededEnum a)) @(8 - SizeOf (EmbededEnum a))
    . embed @Word8
    . fromIntegral @_ @Word8
    . fromEnum
  reify v
    = toEnum
    . fromIntegral
    . reify @Word8
    $ v V.++ V.repeat @(8 - SizeOf (EmbededEnum a)) False

