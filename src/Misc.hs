module Misc where

import Diagrams.Prelude
import Backend

dualInput :: IsName a => a -> Diagram B
dualInput name = input 1 "in0" <> input (-1) "in1"
  where
    input d n = (mkCon (name, n) ||| inputWire) # translate (r2 (0, spacing * d))
    spacing = 0.25

inputWire :: Diagram B
inputWire = fromOffsets [unitX] # scale 0.5

spacer :: Diagram B
spacer = nothing # withEnvelope (rect 0.5 0.5 :: D V2 Double)

vspacer :: Diagram B
vspacer = strut unitY

sspacer :: Diagram B
sspacer = spacer # scale 0.5

svspacer :: Diagram B
svspacer = vspacer # scale 0.5

ssvspacer :: Diagram B
ssvspacer = svspacer # scale 0.5

labelSize = 0.3
textSize = 0.2

mkCon :: IsName a => a -> Diagram B
mkCon name = nothing # named name

con :: IsName a => a -> Diagram B
con name = circle 0.05 # fc black <> mkCon name

nothing :: Diagram B
nothing = pointDiagram $ mkP2 0 0
