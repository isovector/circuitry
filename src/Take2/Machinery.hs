module Take2.Machinery
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
import Take2.Circuit as X
import Take2.Coproduct as X
import Take2.Embed as X
import Take2.Graph as X (RenderOptions (..))
import Take2.Instances as X
import Take2.Numeric as X
import Take2.Primitives as X (nandGate, mapFoldVC, zipVC, cloneV, fixC, foldVC, pad, diagrammed, binaryGateDiagram, unaryGateDiagram, transposeV, tribuf, crossV, unsafeShort, shortcircuit, pullDown, pullUp, traceC, replicateC)
import Take2.Product as X
import Take2.Signal as X (Time)
import Take2.Word as X
import Test.QuickCheck as X (Property, Arbitrary(..), CoArbitrary(..), Function(..), property, (===), forAllShrink, counterexample, quickCheck, resize, oneof, applyFun, functionMap)

