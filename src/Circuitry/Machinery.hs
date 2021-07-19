module Circuitry.Machinery
  ( module X
  , Vec (..)
  ) where

import Circuitry.Category as X
import Circus.Types as X (renderModuleString)
import Clash.Sized.Vector (Vec (..))
import Data.Generics.Labels ()
import Data.Word as X
import GHC.Generics as X (Generic)
import GHC.TypeLits as X (type (+), type (-), type (^), type (<=), KnownNat)
import Circuitry.Circuit as X
import Circuitry.Coproduct as X
import Circuitry.Embed as X
import Circuitry.Graph as X (RenderOptions (..), synthesizeBits)
import Circuitry.Instances as X
import Circuitry.Numeric as X
import Circuitry.Primitives as X (nandGate, mapFoldVC, zipVC, cloneV, fixC, foldVC, pad, diagrammed, binaryGateDiagram, unaryGateDiagram, transposeV, tribuf, crossV, unsafeShort, shortcircuit, pullDown, pullUp, traceC, replicateC)
import Circuitry.Product as X
import Circuitry.Signal as X (Time)
import Circuitry.Word as X
import Test.QuickCheck as X (Property, Arbitrary(..), CoArbitrary(..), Function(..), property, (===), forAllShrink, counterexample, quickCheck, resize, oneof, applyFun, functionMap)

