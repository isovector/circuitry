{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedLabels     #-}

module Take2.Graph where

import           Circuitry.Category (Category(..))
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Lens ((%~), (+~), (<>~))
import           Control.Monad.Reader (ReaderT, MonadReader)
import           Control.Monad.State
import           Data.Generics.Labels ()
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Text as T
import           GHC.Generics
import           Generics.SYB hiding (Generic)
import           Prelude hiding ((.), id, sum)
import           Take2.Embed
import           Yosys (Bit, Cell (..), Module (Module), CellName (..), getBit)


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

