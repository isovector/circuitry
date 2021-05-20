{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE OverloadedLabels           #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wredundant-constraints #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Take2 where

import Test.QuickCheck
import           Circuitry.Category hiding (Catalyst)
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Lens hiding (_Wrapped, _Unwrapped, (:>))
import           Control.Monad.State
import           Data.Data (Proxy(Proxy))
import           Data.Generics.Labels
import           Data.Generics.Wrapped ( _Unwrapped )
import           Data.Typeable
import           Data.Void (Void)
import           GHC.Generics
import           GHC.TypeLits
import           Prelude hiding ((.), id)
import           Unsafe.Coerce (unsafeCoerce)
import Data.Foldable (traverse_)


newtype Port = Port { getPort :: Int }
  deriving stock Generic

data Ports p t where
  UnitP :: Ports () t
  BoolP :: t -> Ports Bool t
  PairP :: Ports a t -> Ports b t -> Ports (a, b) t
  VectorP :: (KnownNat n) => Vec n (Ports a t) -> Ports (Vec n a) t
  EitherP :: t -> [t] -> Ports (Either a b) t

data Machine a b = Machine
  { mach_fast :: a -> b
  , mach_impl :: [Bool] -> [Bool]
  }

notMachine :: Machine Bool Bool
notMachine = Machine not $ \[b] -> [not b]

andMachine :: Machine (Bool, Bool) Bool
andMachine = Machine (uncurry (&&)) $ \[a, b] -> [a && b]

prop_machine :: forall a b. (Arbitrary a, Show b, Eq b, Embed a, Embed b) => Machine a b -> Property
prop_machine m = property $ do
  a <- arbitrary @a
  pure $ mach_fast m a === reify (mach_impl m $ embed a)







class Embed a where
  sizeOf :: Int
  embed :: a -> [Bool]
  reify :: [Bool] -> a

instance Embed () where
  sizeOf = 0
  embed () = []
  reify [] = ()
  reify _ = error "embedded unit was too big"

instance Embed Bool where
  sizeOf = 1
  embed = pure
  reify [b] = b
  reify _ = error "embedded bool was too big"

instance (Embed a, Embed b) => Embed (a, b) where
  sizeOf = sizeOf @a + sizeOf @b
  embed (a, b) = embed a <> embed b
  reify v =
    let (a, b) = splitAt (sizeOf @a) v
     in (reify a, reify b)

instance (Embed a, Embed b) => Embed (Either a b) where
  sizeOf = 1 + max (sizeOf @a) (sizeOf @b)
  embed (Left a) = False : (pad (max (sizeOf @a) (sizeOf @b)) $ embed a)
  embed (Right b) = True : (pad (max (sizeOf @a) (sizeOf @b)) $ embed b)
  reify (False : bs) = Left  $ reify $ take (sizeOf @a) bs
  reify (True : bs)  = Right $ reify $ take (sizeOf @b) bs
  reify [] = error "no tag bit"

prop_embedRoundtrip :: forall a. (Show a, Eq a, Embed a, Arbitrary a) => Property
prop_embedRoundtrip = property $ do
  a <- arbitrary @a
  pure $ a === reify (embed a)

prop_embedSize :: forall a. (Embed a, Arbitrary a) => Property
prop_embedSize = property $ do
  a1 <- arbitrary @a
  a2 <- arbitrary @a
  pure $ length (embed a1) === length (embed a2)

main :: IO ()
main = do
  traverse_ quickCheck
    [ prop_embedRoundtrip @()
    , prop_embedRoundtrip @Bool
    , prop_embedRoundtrip @(Either Bool ())
    , prop_embedRoundtrip @(Either () ())
    , prop_embedRoundtrip @(Either (Either Bool Bool) (Either Bool Bool))
    , prop_embedRoundtrip @(Vec 10 Bool)
    , prop_embedRoundtrip @(Vec 10 (Vec 10 Bool))
    , prop_embedRoundtrip @(Vec 10 (Either Bool Bool))
    , prop_embedSize @()
    , prop_embedSize @Bool
    , prop_embedSize @(Either Bool ())
    , prop_embedSize @(Either (Either Bool Bool) (Either Bool Bool))
    , prop_embedSize @(Vec 10 Bool)
    , prop_embedSize @(Vec 10 (Vec 10 Bool))
    , prop_embedSize @(Vec 10 (Either Bool Bool))
    , prop_machine notMachine
    , prop_machine andMachine
    ]

pad :: Int -> [Bool] -> [Bool]
pad n ix = ix <> replicate (n - length ix) False

instance (Embed a, KnownNat n) => Embed (Vec n a) where
  sizeOf = sizeOf @a * fromInteger (natVal $ Proxy @n)
  embed vec = join $ V.toList $ fmap embed vec
  reify = V.unsafeFromList . fmap reify . chunksOf (sizeOf @a)


chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = map (take i) (build (splitter ls)) where
  build g = g (:) []
  splitter :: [e] -> ([e] -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n  = l `c` splitter (drop i l) c n


instance Category Graph where
  type Ok Graph = Embed
  id = Graph pure
  Graph g . Graph f = Graph (g <=< f)

-- instance SymmetricProduct Graph where
--   swap = genComp "swap"
--   reassoc = genComp "reassoc"

-- instance MonoidalProduct Graph where
--   first' c = Graph $ \(PairP ap bp) -> do
--     cout <- mkComp "first" ap
--     pure $ PairP cout bp

-- instance Cartesian Graph where
--   consume = genComp "consume"
--   copy = genComp "copy"
--   fst' = genComp "fst"
--   snd' = genComp "snd"



class GenPorts a where
  genPorts :: GraphM (Ports a Port)

instance GenPorts () where
  genPorts = pure UnitP

instance GenPorts Bool where
  genPorts = fmap BoolP freshPort

instance (GenPorts a, GenPorts b) => GenPorts (a, b) where
  genPorts = PairP <$> genPorts <*> genPorts

instance (GenPorts a, KnownNat n) => GenPorts (Vec n a) where
  genPorts = fmap VectorP $ V.traverse# id $ V.repeat genPorts

instance (GenPorts a, GenPorts b) => GenPorts (Either a b) where
  genPorts = undefined




newtype Graph a b = Graph
  { unGraph :: Ports a Port -> GraphM (Ports b Port)
  }

genComp :: GenPorts b => String -> Graph a b
genComp = Graph . mkComp


mkComp :: GenPorts b => String -> Ports a Port -> GraphM (Ports b Port)
mkComp name pa = do
  pb <- genPorts
  modify $ #gs_components %~ (Component name pa pb :)
  pure pb


data Component t where
  Component :: String -> Ports a t -> Ports b t -> Component t


freshPort :: GraphM Port
freshPort = do
  p <- gets gs_next_port
  modify $ #gs_next_port . _Unwrapped +~ 1
  pure p


data GraphState = GraphState
  { gs_next_port :: Port
  , gs_components :: [Component Port]
  }
  deriving stock (Generic)

newtype GraphM a = GraphM { unGraphM :: State GraphState a }
  deriving newtype (Functor, Applicative, Monad, MonadState GraphState)


