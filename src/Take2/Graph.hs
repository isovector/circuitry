{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Graph where

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
import           Test.QuickCheck
import           Unsafe.Coerce (unsafeCoerce)

newtype Port = Port { getPort :: Int }
  deriving stock Generic

data Ports p t where
  UnitP :: Ports () t
  BoolP :: t -> Ports Bool t
  PairP :: Ports a t -> Ports b t -> Ports (a, b) t
  VectorP :: (KnownNat n) => Vec n (Ports a t) -> Ports (Vec n a) t
  EitherP
      :: MaxProof (SizeOf a) (SizeOf b)
      -> t
      -> Ports (Vec (Max (SizeOf a) (SizeOf b)) Bool) t
      -> Ports (Either a b) t

instance GenPorts Word8 where
  genPorts = undefined


instance Functor (Ports p) where
  fmap _ UnitP = UnitP
  fmap fab (BoolP a) = BoolP (fab a)
  fmap fab (PairP po' po_ba) = PairP (fmap fab po') (fmap fab po_ba)
  fmap fab (VectorP v) = VectorP $ fmap (fmap fab) v
  fmap fab (EitherP proof t p) = EitherP proof (fab t) $ fmap fab p


class (GenPorts a, KnownNat (SizeOf a)) => Stuff a
instance (GenPorts a, KnownNat (SizeOf a)) => Stuff a



instance Category Graph where
  type Ok Graph = Stuff
  id = Graph pure
  Graph g . Graph f = Graph (g <=< f)

-- instance SymmetricProduct Graph where
--   swap = genComp "swap"
--   reassoc = genComp "reassoc"

-- instance MonoidalProduct Graph where
--   first' _ = Graph $ \(PairP p bp) -> do
--     cout <- mkComp "first" p
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

instance (Stuff a, Stuff b, KnownNat (Bigger a b)) => GenPorts (Either a b) where
  genPorts = EitherP <$> pure (maxProof @a @b) <*> freshPort <*> genPorts




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


