{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Take2.Circuit where

import Circuitry.Catalyst (Roar(..), Time)
import Circuitry.Category (Category(..))
import Data.Generics.Labels ()
import Prelude hiding ((.), id)
import Take2.Embed
import Take2.Graph


data Circuit a b = Circuit
  { c_graph :: Graph a b
  , c_roar :: Roar Time a b
  }

instance Category Circuit where
  type Ok Circuit = OkCircuit
  id = Circuit id id
  Circuit gg gr . Circuit fg fr = Circuit (gg . fg) (gr . fr)


evalCircuit :: Circuit a b -> Time -> a -> b
evalCircuit c t a = runRoar (c_roar c) (const a) t


evalCircuitT :: Circuit a b -> (Time -> a) -> Time -> b
evalCircuitT c a t = runRoar (c_roar c) (a) t


class (Stuff a, Embed a) => OkCircuit a
instance (Stuff a, Embed a) => OkCircuit a

