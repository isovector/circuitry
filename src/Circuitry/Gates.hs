module Circuitry.Gates where

import Control.Arrow (second)
import Diagrams.Prelude

import Circuitry.Backend
import Circuitry.Misc
import Circuitry.Types

andGate :: DiaID s -> Diagram B
andGate = andGate' inputWire inputWire

andGate' :: Diagram B -> Diagram B -> DiaID s -> Diagram B
andGate' a b n = dualInput' a b n
      ||| roundedRect' 1.2 1 (with & radiusBR .~ 0.5
                                   & radiusTR .~ 0.5
                                   )
      ||| mkCon n (Out 0)

orGate :: DiaID s -> Diagram B
orGate = orGate' inputWire inputWire

orGate' :: Diagram B -> Diagram B -> DiaID s -> Diagram B
orGate' a b n = ( dualInput' a b n
        <> shape # translate (r2 (0.85, 0))
         ) ||| mkCon n (Out 0)
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

xorGate :: DiaID s -> Diagram B
xorGate = xorGate' inputWire inputWire

xorGate' :: Diagram B -> Diagram B -> DiaID s -> Diagram B
xorGate' a b n = ( dualInput' a b n
        <> shape # translate (r2 (0.85, 0))
         ) ||| mkCon n (Out 0)
  where
    line = fromOffsets [unitX] # scale 0.5
    shape = cubicSpline False (fmap p2 [(-0.5, 0.5), (-0.3, 0), (-0.5, -0.5)])
        ||| (cubicSpline False (fmap p2 [(-0.5, 0.5), (-0.3, 0), (-0.5, -0.5)])
         <> topBot
         <> cubicSpline False (fmap p2 splineBits)
         <> cubicSpline False (fmap (p2 . second negate) splineBits))
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
notGate n = mkCon n (In 0) ||| inputWire ||| triangle 1 # rotate (-1/4 @@ turn) ||| smallNot ||| mkCon n (Out 0)

dualInput' :: Diagram B -> Diagram B -> DiaID s -> Diagram B
dualInput' a b name = input a 1 0 <> input b (-1) 1
  where
    input x d n = (mkCon name (In n) ||| x) # translate (r2 (0, spacing * d))
    spacing = 0.25

dualInput :: DiaID s -> Diagram B
dualInput = dualInput' inputWire inputWire


input :: DiaID s -> Diagram B
input name = mkCon name (In 0) ||| inputWire ||| mkCon name (Out 0)

