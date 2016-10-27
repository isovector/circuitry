module Gates where

import Control.Arrow (second)
import Backend
import Diagrams.Prelude
import Misc

andGate :: IsName a => a -> Diagram B
andGate name = dualInput name
           ||| roundedRect' 1.2 1 (with & radiusBR .~ 0.5
                                        & radiusTR .~ 0.5
                                        )
           ||| mkCon (name, "out0")

orGate :: IsName a => a -> Diagram B
orGate name = ( dualInput name
             <> shape # translate (r2 (0.85, 0))
              ) ||| mkCon (name, "out0")
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

nandGate :: IsName a => a -> Diagram B
nandGate name = andGate name ||| smallNot

norGate :: IsName a => a -> Diagram B
norGate name = orGate name ||| smallNot

smallNot :: Diagram B
smallNot = circle 0.08

notGate :: IsName a => a -> Diagram B
notGate name = dualInput name ||| triangle 1 # rotate (-1/4 @@ turn) ||| smallNot ||| mkCon (name, "out")
