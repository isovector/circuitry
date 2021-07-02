{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

{-# OPTIONS_GHC -Wall                   #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module Take2.Embed where

import           Circuitry.Category (Category(..))
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable hiding (sum)
import           Data.Generics.Labels ()
import           Data.Typeable
import           Data.Word (Word8)
import           GHC.Generics
import           GHC.TypeLits
import           GHC.TypeLits.Extra
import           Prelude hiding ((.), id, sum)
import           Take2.Word


class KnownNat (SizeOf a) => Embed a where
  type SizeOf a :: Nat
  type SizeOf a = GSizeOf (Rep a)
  embed :: a -> Vec (SizeOf a) Bool
  default embed :: (SizeOf a ~ GSizeOf (Rep a), GEmbed (Rep a), Generic a) => a -> Vec (SizeOf a) Bool
  embed = gembed . from
  reify :: Vec (SizeOf a) Bool -> a
  default reify :: (SizeOf a ~ GSizeOf (Rep a), GEmbed (Rep a), Generic a) => Vec (SizeOf a) Bool -> a
  reify = to . greify

{-# RULES
"embed . reify" forall a. embed (reify a) = a
"reify . embed" forall a. reify (embed a) = a
"gembed . greify" forall a. gembed (greify a) = a
"greify . gembed" forall a. greify (gembed a) = a
#-}


class KnownNat (GSizeOf f) => GEmbed f where
  type GSizeOf f :: Nat
  gembed :: f x -> Vec (GSizeOf f) Bool
  greify :: Vec (GSizeOf f) Bool -> f x

instance GEmbed f => GEmbed (M1 _1 _2 f) where
  type GSizeOf (M1 _1 _2 f) = GSizeOf f
  gembed = gembed . unM1
  greify = M1 . greify
  {-# INLINE[~2] gembed #-}
  {-# INLINE[~2] greify #-}

instance GEmbed U1 where
  type GSizeOf U1 = 0
  gembed U1 = Nil
  greify _ = U1
  {-# INLINE[~2] gembed #-}
  {-# INLINE[~2] greify #-}

instance Embed a => GEmbed (K1 _1 a) where
  type GSizeOf (K1 _1 a) = SizeOf a
  gembed = embed . unK1
  greify = K1 . reify
  {-# INLINE[~2] gembed #-}
  {-# INLINE[~2] greify #-}

instance (GEmbed f, GEmbed g) => GEmbed (f :*: g) where
  type GSizeOf (f :*: g) = GSizeOf f + GSizeOf g
  gembed (f :*: g) = gembed f V.++ gembed g
  greify v =
    let (a, b) = V.splitAtI v
     in greify a :*: greify b
  {-# INLINE[~2] gembed #-}
  {-# INLINE[~2] greify #-}

instance (GEmbed f, GEmbed g) => GEmbed (f :+: g) where
  type GSizeOf (f :+: g) = Max (GSizeOf f) (GSizeOf g) + 1
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
  {-# INLINE[~2] gembed #-}
  {-# INLINE[~2] greify #-}


instance Embed ()
instance Embed a => Embed (Maybe a)

instance Embed Word4 where
  type SizeOf Word4 = 4
  embed w8 =
    let t = B.testBit w8
     in t 0 :> t 1 :> t 2 :> t 3 :> Nil
  reify (b0 :> b1 :> b2 :> b3 :> Nil) =
    let s b = B.shiftL (bool 0 1 b)
     in foldr @[] (B..|.) 0 $ zipWith s [b0, b1, b2, b3 ] [0..]
  reify _ = error "impossible"
  {-# INLINE[~2] embed #-}
  {-# INLINE[~2] reify #-}

instance Embed Word8 where
  type SizeOf Word8 = 8
  embed w8 =
    let t = B.testBit w8
     in t 0 :> t 1 :> t 2 :> t 3 :> t 4 :> t 5 :> t 6 :> t 7 :> Nil
  reify (b0 :> b1 :> b2 :> b3 :> b4 :> b5 :> b6 :> b7 :> Nil) =
    let s b = B.shiftL (bool 0 1 b)
     in foldr @[] (B..|.) 0 $ zipWith s [b0, b1, b2, b3, b4, b5, b6, b7] [0..]
  reify _ = error "impossible"
  {-# INLINE[~2] embed #-}
  {-# INLINE[~2] reify #-}

instance Embed Bool

instance (Embed a, Embed b) => Embed (a, b)

instance (Embed a, KnownNat n) => Embed (Vec n a) where
  type SizeOf (Vec n a) = n * SizeOf a
  embed = V.concatMap embed
  reify = V.map reify . V.unconcatI
  {-# INLINE[~2] embed #-}
  {-# INLINE[~2] reify #-}

instance (Embed a, Embed b) => Embed (Either a b)


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
{-# INLINE withSomeNat #-}

type Bigger a b = Max (SizeOf a) (SizeOf b)

