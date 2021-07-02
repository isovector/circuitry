{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RoleAnnotations #-}

module Take2.Circuit where


import           Circuitry.Catalyst (Signal, Time, pumpSignal)
import           Circuitry.Category (Category(..))
import qualified Clash.Sized.Vector as V
import           Control.Monad (join)
import           Control.Monad.State (evalState, gets)
import           Data.Foldable (for_)
import           Data.Generics.Labels ()
import qualified Data.Map as M
import qualified Data.Text as T
import           Data.Typeable
import           GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import           Prelude hiding ((.), id)
import           Take2.Embed
import           Take2.Graph
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


reallyPumpSignal :: Signal a b -> (Time -> a) -> Time -> b
reallyPumpSignal sig f 0 = snd $ pumpSignal sig (f 0)
reallyPumpSignal sig f n = reallyPumpSignal (fst $ pumpSignal sig (f 0)) (f . (+ 1)) (n - 1)


evalCircuit :: Circuit a b -> a -> Time -> b
evalCircuit c a t = evalCircuitT c (const a) t


evalCircuitT :: Circuit a b -> (Time -> a) -> Time -> b
evalCircuitT c = reallyPumpSignal (c_roar c)


getGraph :: forall a b. (SeparatePorts a, SeparatePorts b) => Circuit a b -> Module
getGraph c = flip evalState (GraphState 0 mempty) $ unGraphM $ do
  (input, ips) <- separatePorts @a
  (output, ops) <- separatePorts @b
  output' <- unGraph (c_graph c) input
  for_ (V.toList $ V.zip output' output) $ uncurry unifyBits
  m <- gets gs_module

  let mkPort :: Direction -> String -> Int -> (PortName, [Y.Bit]) -> (PortName, Port)
      mkPort dir pre ix (PortName pn, bits) =
        ( PortName (T.pack (pre <> show ix <> " : ") <> pn)
        , Port dir bits
        )

  pure $ m <> mempty
    { modulePorts =
        M.fromList $ fmap (uncurry $ mkPort Input "in") (zip [0..] ips)
                  <> fmap (uncurry $ mkPort Output "out") (zip [0..] ops)
    }


newtype Named (n :: Symbol) a = Named a
  deriving stock (Eq, Ord, Show, Functor)
  deriving newtype Embed



class Embed a => OkCircuit a
instance Embed a => OkCircuit a


class SeparatePorts a where
  separatePorts :: GraphM (V.Vec (SizeOf a) Y.Bit, [(PortName, [Y.Bit])])

instance {-# OVERLAPPABLE #-} (Typeable a, Embed a) => SeparatePorts a where
  separatePorts = do
    b <- synthesizeBits @a
    pure
      ( b
      , [ ( Y.PortName $ T.pack $ show $ typeRep $ Proxy @a
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



