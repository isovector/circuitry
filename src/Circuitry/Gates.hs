module Circuitry.Gates where

import Control.Arrow (second)
import Diagrams.Prelude

import Circuitry.Backend
import Circuitry.Misc
import Circuitry.Types

andGate :: DiaID s -> Diagram B
andGate n = dualInput n
      ||| roundedRect' 1.2 1 (with & radiusBR .~ 0.5
                                   & radiusTR .~ 0.5
                                   )
      ||| mkCon' n (Out 0)

orGate :: DiaID s -> Diagram B
orGate n = ( dualInput n
        <> shape # translate (r2 (0.85, 0))
         ) ||| mkCon' n (Out 0)
  where
    line = fromOffsets [unitX] # scale 0.5
    shape = cubicSpline False (fmap p2 [(-0.5, 0.5), (-0.3, 0), (-0.5, -0.5)])
         <> topBot
         <> cubicSpline False (fmap p2 splineBits)
         <> cubicSpline False (fmap (p2 . second negate) splineBits)
    splineBits = [(0.0, 0.5), (0.2, 0.4), (0.4, 0.2), (0.5, 0)]
    topBot = ( line # translate (r2 (0, -0.5))
            <> line # translate (r2 (0, 0.5))
             ) # translate (r2 (-0.5, 0))

nandGate :: DiaID s -> Diagram B
nandGate = (||| smallNot) . andGate

norGate :: DiaID s -> Diagram B
norGate = (||| smallNot) . orGate

smallNot :: Diagram B
smallNot = circle 0.08

notGate :: DiaID s -> Diagram B
notGate n = dualInput n ||| triangle 1 # rotate (-1/4 @@ turn) ||| smallNot ||| mkCon' n (Out 0)

dualInput :: DiaID s -> Diagram B
dualInput name = input 1 0 <> input (-1) 1
  where
    input d n = (mkCon' name (In n) ||| inputWire) # translate (r2 (0, spacing * d))
    spacing = 0.25

mkCon' :: DiaID s -> Port -> Diagram B
mkCon' d p = mkCon (show d, p)
