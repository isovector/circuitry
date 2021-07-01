{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Circuit where

import Circuitry.Catalyst (Signal, Time, pumpSignal)
import Circuitry.Category (Category(..))
import Data.Generics.Labels ()
import Prelude hiding ((.), id)
import Take2.Embed
import Take2.Graph


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


class (Stuff a, Embed a) => OkCircuit a
instance (Stuff a, Embed a) => OkCircuit a

