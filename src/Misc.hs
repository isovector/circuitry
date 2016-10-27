module Misc where

import Diagrams.Prelude
import Backend
import Types
import DSL

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
mkCon n = nothing # named n

con :: DiaID s -> Diagram B
con n = circle 0.05 # fc black <> mkCon (show n, Split)

nothing :: Diagram B
nothing = pointDiagram $ mkP2 0 0

splitting :: (FoundPort s Double -> DSL s B Double Any a) -> DSL s B Double Any a
splitting f = do
    d <- liftDia con
    p <- getPort d Split
    f p

