{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Circuit where


import           Circuitry.Catalyst (Signal, Time, pumpSignal)
import           Circuitry.Category (Category(..))
import qualified Clash.Sized.Vector as V
import           Control.Monad.State (evalState, gets)
import           Data.Generics.Labels ()
import qualified Data.Map as M
import           Prelude hiding ((.), id)
import           Take2.Embed
import           Take2.Graph
import           Yosys (Module, modulePorts, Port (Port), Direction (Input, Output), PortName (PortName))
import Data.Typeable
import qualified Data.Text as T
import Debug.Trace (traceM)


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


getGraph :: forall a b. (Typeable a, Typeable b, Embed a, Embed b) => Circuit a b -> Module
getGraph c = flip evalState (GraphState 0 mempty) $ unGraphM $ do
  input <- synthesizeBits @a
  output <- unGraph (c_graph c) input
  m <- gets gs_module
  pure $ m <> mempty
    { modulePorts = M.fromList
        [ ( PortName $ mappend "in: " $ T.pack $ show $ typeRep $ Proxy @a
          , Port Input $ V.toList input
          )
        , ( PortName $ mappend "out: " $ T.pack $ show $ typeRep $ Proxy @b
          , Port Output $ V.toList output
          )
        ]
    }



class (Embed a) => OkCircuit a
instance (Embed a) => OkCircuit a

