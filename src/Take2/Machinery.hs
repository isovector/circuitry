module Take2.Machinery
  ( module Take2.Machinery
  , module X
  , Vec (..)
  ) where

import Circuitry.Catalyst (Roar(Roar))
import Circuitry.Category as X
import Take2.Circuit as X
import Take2.Instances as X
import Take2.Primitives as X (nandGate, mapFoldVC, zipVC, cloneV, fixC, foldVC, pad, coerceCircuit, diagrammed, binaryGateDiagram, unaryGateDiagram)
import Clash.Sized.Vector (Vec (..))

