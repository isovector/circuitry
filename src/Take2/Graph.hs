{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Graph where

import           Circuitry.Catalyst (Time)
import           Circuitry.Category (Category(..), first', swap, (&&&), (>>>), swapE, SymmetricProduct (reassoc), MonoidalProduct (second'), Cartesian(..), SymmetricSum(..), MonoidalSum)
import           Circuitry.Category (MonoidalProduct(..))
import           Circuitry.Category (MonoidalSum(..))
import           Circuitry.Category (SymmetricProduct(..))
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Lens ((%~), (+~), (<>~))
import           Control.Monad.Reader (ReaderT, MonadReader)
import           Control.Monad.State
import qualified Data.Bits as B
import           Data.Bool (bool)
import           Data.Foldable hiding (sum)
import           Data.Generics.Labels ()
import           Data.Generics.Wrapped ( _Unwrapped )
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Profunctor
import qualified Data.Text as T
import           Data.Traversable
import           Data.Typeable
import           Data.Word (Word8, Word16, Word32, Word64)
import           GHC.Generics
import           GHC.TypeLits
import           GHC.TypeLits.Extra
import           Generics.SYB hiding (Generic)
import           Prelude hiding ((.), id, sum)
import           Take2.Embed
import           Test.QuickCheck
import           Unsafe.Coerce (unsafeCoerce)
import           Yosys (Bit, Module (Module), Cell (Cell), CellName (..), getBit)
import qualified Yosys as Y




newtype Graph a b = Graph
  { unGraph :: Vec (SizeOf a) Bit -> GraphM (Vec (SizeOf b) Bit)
  }

instance Category Graph where
  type Ok Graph = Embed
  id = Graph pure
  Graph g . Graph f = Graph (g <=< f)


coerceGraph
    :: (SizeOf a ~ SizeOf a', SizeOf b ~ SizeOf b')
    => Graph a b
    -> Graph a' b'
coerceGraph = Graph . unGraph

unifyBitsImpl :: Data a => Map Bit Bit -> a -> a
unifyBitsImpl rep  = everywhere $ mkT $ \case
  b | Just b' <- M.lookup b rep -> b'
    | otherwise -> b

unifyBits :: Map Bit Bit -> GraphM ()
unifyBits rep = modify' $ #gs_module %~ unifyBitsImpl rep


freshBit :: GraphM Bit
freshBit = do
  p <- gets gs_next_port
  modify $ #gs_next_port +~ 1
  pure p


addNamedCell :: CellName -> Cell -> GraphM ()
addNamedCell name c = do
  modify $
    #gs_module <>~
      Module mempty
        (M.singleton name c)

addCell :: Cell -> GraphM ()
addCell c = do
  name <- freshBit
  addNamedCell (CellName $ T.pack $ show $ getBit name) c

synthesizeBits :: (Embed a) => GraphM (Vec (SizeOf a) Bit)
synthesizeBits = flip V.traverse# (V.repeat ()) $ const freshBit


data GraphState = GraphState
  { gs_next_port :: Bit
  , gs_module    :: Module
  }
  deriving stock (Generic)

data RenderOptions = RenderOptions
  { ro_unpack_gates :: Bool
  , ro_unpack_constants :: Bool
  , ro_depth :: Int
  }
  deriving stock (Eq, Ord, Show, Generic)

newtype GraphM a = GraphM { unGraphM :: ReaderT RenderOptions (State GraphState) a }
  deriving newtype ( Functor
                   , Applicative
                   , Monad
                   , MonadState GraphState
                   , MonadReader RenderOptions
                   , MonadFix
                   )

