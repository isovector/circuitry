module Take2.Machinery
  ( module Take2.Machinery
  , module X
  , Vec (..)
  ) where

import Circuitry.Catalyst (Roar(Roar))
import Circuitry.Category as X hiding (distrib)
import Take2.Circuit as X
import Take2.Instances as X
import Take2.Primitives as X (nandGate, mapFoldVC, zipVC, cloneV, fixC, foldVC, constC)
import Clash.Sized.Vector (Vec (..))

------------------------------------------------------------------------------
-- | Too slow to run real world physics? JET STREAM IT, BABY.
shortcircuit :: (a -> b) -> Circuit a b -> Circuit a b
shortcircuit f c = Circuit (c_graph c) $ Roar $ \fa t -> f (fa t)

