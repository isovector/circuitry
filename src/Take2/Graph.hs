{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedLabels     #-}

module Take2.Graph where

import           Circuitry.Category (Category(..))
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Monad.Reader (ReaderT, MonadReader)
import           Control.Monad.State
import           Data.Generics.Labels ()
import           GHC.Generics
import           Prelude hiding ((.), id, sum)
import           Take2.Embed
import           Circus.Types (Bit)
import           Circus.DSL


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


synthesizeBits :: (Embed a) => GraphM (Vec (SizeOf a) Bit)
synthesizeBits = flip V.traverse# (V.repeat ()) $ const freshBit


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

