{-# LANGUAGE AllowAmbiguousTypes  #-}
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
import           Control.Lens ((%~), (+~), (<>~))
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
import           Prelude hiding ((.), id, sum)
import           Take2.Embed
import           Test.QuickCheck
import           Unsafe.Coerce (unsafeCoerce)
import           Yosys (Bit, Module (Module), Cell (Cell), CellName (..), getBit)




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



freshBit :: GraphM Bit
freshBit = do
  p <- gets gs_next_port
  modify $ #gs_next_port +~ 1
  pure p


addCell :: Cell -> GraphM ()
addCell c = do
  name <- freshBit
  modify $
    #gs_module <>~
      Module mempty
        (M.singleton (CellName $ T.pack $ show $ getBit name) c)

synthesizeBits :: (1 <= SizeOf a, Embed a) => GraphM (Vec (SizeOf a) Bit)
synthesizeBits = for (V.repeat ()) $ const freshBit


data GraphState = GraphState
  { gs_next_port :: Bit
  , gs_module    :: Module
  }
  deriving stock (Generic)

newtype GraphM a = GraphM { unGraphM :: State GraphState a }
  deriving newtype (Functor, Applicative, Monad, MonadState GraphState)


