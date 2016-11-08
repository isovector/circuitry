{-# LANGUAGE GADTs #-}
module Circuitry.Misc where

import Diagrams.Prelude
import Circuitry.Backend
import Circuitry.Types
import Circuitry

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

mkCon :: DiaID s -> Port -> Diagram B
mkCon d p = nothing # named (show d, p)

con :: DiaID s -> Diagram B
con n = circle 0.05 # fc black <> mkCon n Split

bend :: DiaID s -> Diagram B
bend n = mkCon n Split

nothing :: Diagram B
nothing = pointDiagram $ mkP2 0 0

anon :: (DiaID s -> Diagram B)
     -> ((DiaID s, FoundPort s Double) -> Circuit s B Double Any a)
     -> Circuit s B Double Any a
anon t f = do
    d <- liftDia t
    p <- getPort d Split
    f (d, p)

labeled :: String -> Diagram B -> Diagram B
labeled label d = ( d # center
                 <> rect (width d - 0.5) (height d + 0.25) # lw veryThick
                  ) === svspacer === text label # scale labelSize

wireLabel :: String -> Diagram B
wireLabel s = text s # scale textSize # translate (r2 (0, 0.2))

labeledWire :: String -> Diagram B
labeledWire s = wireLabel s <> inputWire

typedWire :: String -> Diagram B
typedWire s = wireLabel s # translateX 0.2 <> inputWire

polyIn :: Diagram B
polyIn = pline 3 <> pline 2 <> pline 1
  where
    pline h = fromOffsets [unitY] # scale (0.1*h) # translate (r2 ((-0.05) * h, (-0.1 / 2) * h))

polyOut :: Diagram B
polyOut = polyIn # rotate (1/2 @@ turn)

wire :: DiaID s -> Diagram B
wire s = mkCon s (In 0) ||| inputWire ||| mkCon s (Out 0)

vwire :: DiaID s -> Diagram B
vwire s = (mkCon s (In 0) ||| inputWire ||| mkCon s (Out 0)) # rotate (-1/4 @@ turn)

multiIn :: String -> DiaID s -> Diagram B
multiIn l a = (mkCon a (In 0) <> text "}" # scale 0.5 # translateY (-0.003) # translateX 0.1) ||| inputWire ||| wireLabel l ||| inputWire ||| mkCon a (Out 0)

inputMulti :: Diagram B
inputMulti = text "}" # scale 0.5 # translateY (-0.003) # translateX 0.1 ||| inputWire

outputMulti :: Diagram B
outputMulti = inputWire # scaleX 0.75 ||| (text "{" # scale 0.5 # translateY (-0.003) # translateX (-0.13) <> nothing)

multiOut :: DiaID s -> Diagram B
multiOut a = mkCon a (In 0) ||| outputMulti ||| mkCon a (Out 0)

nybble :: DiaID s -> Diagram B
nybble s = vsep 0.1 $ fmap (\x -> inputWire ||| mkCon s (Out x)) [3, 2, 1, 0]
