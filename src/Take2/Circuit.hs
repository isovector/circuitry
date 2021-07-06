{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

module Take2.Circuit where


import           Circuitry.Category (Category(..))
import           Clash.Sized.Vector (Vec)
import qualified Clash.Sized.Vector as V
import           Control.Lens ((<>~))
import           Control.Monad (join)
import           Control.Monad.Reader (runReaderT)
import           Control.Monad.State (evalState, gets, modify')
import           Data.Generics.Labels ()
import qualified Data.Map as M
import qualified Data.Text as T
import           Data.Typeable
import           GHC.Generics (Generic)
import           GHC.TypeLits (Symbol, KnownSymbol, symbolVal, natVal)
import           GHC.TypeNats (KnownNat)
import           Prelude hiding ((.), id)
import           Take2.Embed
import           Take2.Graph
import           Take2.Signal
import           Test.QuickCheck.Arbitrary (Arbitrary)
import           Yosys (Module, modulePorts, Port (Port), Direction (Input, Output), PortName (PortName))
import qualified Yosys as Y


data Circuit a b = Circuit
  { c_graph :: Graph a b
  , c_roar :: Signal a b
  }

instance Category Circuit where
  type Ok Circuit = OkCircuit
  id = Circuit id id
  Circuit gg gr . Circuit fg fr = Circuit (gg . fg) (gr . fr)


reallyPumpSignal :: (Embed b, Embed a) => Signal a b -> (Time -> Vec (SizeOf a) (Maybe Bool)) -> Time -> [Vec (SizeOf b) (Maybe Bool)]
reallyPumpSignal sig f 0
  =  pure $ snd $ pumpSignal sig (f 0)
reallyPumpSignal sig f n
  = let (sig', v) = pumpSignal sig (f 0)
     in v : reallyPumpSignal sig' (f . (+ 1)) (n - 1)


evalCircuit :: (Embed b, Embed a) => Circuit a b -> a -> Time -> Maybe b
evalCircuit c a t = evalCircuitT c (const a) t

evalCircuitMV :: (Embed b, Embed a) => Circuit a b -> Vec (SizeOf a) (Maybe Bool) -> Time -> Vec (SizeOf b) (Maybe Bool)
evalCircuitMV c a t = evalCircuitTMV c (const a) t


evalCircuitT :: (Embed b, Embed a) => Circuit a b -> (Time -> a) -> Time -> Maybe b
evalCircuitT c f t = fmap reify $ V.traverse# id $ last $ reallyPumpSignal (c_roar c) (fmap Just . embed . f) t

evalCircuitTT :: (Embed b, Embed a) => Circuit a b -> (Time -> a) -> Time -> [Maybe b]
evalCircuitTT c f t = fmap (fmap reify . V.traverse# id) $ reallyPumpSignal (c_roar c) (fmap Just . embed . f) t

evalCircuitTMV :: (Embed b, Embed a) => Circuit a b -> (Time -> Vec (SizeOf a) (Maybe Bool)) -> Time -> Vec (SizeOf b) (Maybe Bool)
evalCircuitTMV c f t = last $ reallyPumpSignal (c_roar c) f t


getGraph :: forall a b. (SeparatePorts a, SeparatePorts b) => RenderOptions -> Circuit a b -> Module
getGraph ro c
  = flip evalState (GraphState 0 mempty)
  $ flip runReaderT ro
  $ unGraphM
  $ do
    (input, ips) <- separatePorts @a
    (output, ops) <- separatePorts @b

    let mkPort :: Direction -> String -> Int -> (PortName, [Y.Bit]) -> (PortName, Port)
        mkPort dir pre ix (PortName pn, bits) =
          ( PortName (T.pack (pre <> show ix <> " : ") <> pn)
          , Port dir bits
          )

    modify' $ #gs_module <>~
      mempty
        { modulePorts =
            M.fromList $ fmap (uncurry $ mkPort Input "in") (zip [0..] ips)
                      <> fmap (uncurry $ mkPort Output "out") (zip [0..] ops)
        }

    output' <- unGraph (c_graph c) input
    unifyBits $ M.fromList $ V.toList $ V.zip output output'
    fmap Y.simplify $
      gets gs_module


newtype Named (n :: Symbol) a = Named a
  deriving stock (Eq, Ord, Show, Functor)
  deriving newtype Embed



class Embed a => OkCircuit a
instance Embed a => OkCircuit a

class Nameable a where
  nameOf :: String

instance {-# OVERLAPPABLE #-} Typeable a => Nameable a where
  nameOf = show $ typeRep $ Proxy @a

instance (Nameable a, KnownNat n) => Nameable (Vec n a) where
  nameOf = nameOf @a <> "[" <> show (natVal $ Proxy @n) <> "]"

newtype Addr n = Addr { getAddr :: Vec n Bool }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype Arbitrary
  deriving anyclass Embed

class SeparatePorts a where
  separatePorts :: GraphM (V.Vec (SizeOf a) Y.Bit, [(PortName, [Y.Bit])])

instance SeparatePorts () where
  separatePorts = pure (V.Nil, mempty)

instance {-# OVERLAPPABLE #-} (Nameable a, Embed a) => SeparatePorts a where
  separatePorts = do
    b <- synthesizeBits @a
    pure
      ( b
      , [ ( Y.PortName $ T.pack $ nameOf @a
          , V.toList b
          )
        ]
      )

instance (KnownSymbol name, SeparatePorts a) => SeparatePorts (Named name a) where
  separatePorts = do
    (a, b) <- separatePorts @a
    pure (a, pure (PortName $ T.pack (symbolVal $ Proxy @name), join $ fmap snd b))

instance {-# OVERLAPPING #-} (SeparatePorts a, SeparatePorts b) => SeparatePorts (a, b) where
  separatePorts = do
    (va, a) <- separatePorts @a
    (vb, b) <- separatePorts @b
    pure (va V.++ vb,  a <> b)

