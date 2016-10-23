{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Arrow (second)
import Control.Lens hiding ((#), at)
import Data.List (zipWith)
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude
import Diagrams.TwoD.Shapes
import Diagrams.Backend.Canvas.CmdLine

dualInput :: IsName a => a -> Diagram B
dualInput name = input 1 "in0" <> input (-1) "in1"
  where
    input d n = (mkCon (name, n) ||| inputWire) # translate (r2 (0, spacing * d))
    spacing = 0.25

inputWire :: Diagram B
inputWire = fromOffsets [unitX] # scale 0.5

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

machine :: IsName a => a -> [String] -> [String] -> String -> Diagram B
machine name ins outs labelText = inputNumStack ||| inputStack
                              ||| (rect width height <> inLabels <> outLabels <> label)
                              ||| outputStack ||| outputNumStack
  where
    vspacing = 2.5
    hspacing = width / 2 - textSize
    width = (fromIntegral ( maximum (fmap length ins)
                          + maximum (fmap length outs)) * textSize)
          + (fromIntegral (length labelText) * labelSize) + 0.5
    label = text labelText # scale labelSize
    height = minimum [heightOf outs, heightOf ins, negate $ textSize + 0.2]
    -- TODO(sandy): this is negative. wtf?
    heightOf ls = -vspacing * fromIntegral (length ls - 1) / 2
    stack as = foldl (\b a -> b # translate (r2 (0, vspacing)) <> a) nothing as

    objStack as f = stack (fmap f as) # translate (r2 (0, heightOf as)) # scaleY textSize

    inputNumStack  = objStack (renumber ins) $ \a -> mkCon (name, "in" ++ a)
    inputStack     = objStack ins $ \a -> mkCon (name, a) ||| inputWire
    outputStack    = objStack outs $ \a -> mkCon (name, a)
    outputNumStack = objStack (renumber outs) $ \a -> mkCon (name, "out" ++ a)
    textStack ls   = stack (fmap text ls) # translate (r2 (0, heightOf ls)) # scale textSize

    inLabels  = textStack ins # translate (r2 (-hspacing, 0))
    outLabels = textStack outs # translate (r2 (hspacing, 0))

    renumber = zipWith ((show .) . const) [0..]

polyIn :: Diagram B
polyIn = pline 3 <> pline 2 <> pline 1
  where
    pline h = fromOffsets [unitY] # scale (0.1*h) # translate (r2 ((-0.05) * h, (-0.1 / 2) * h))

smallNot :: Diagram B
smallNot = circle 0.08

notGate :: IsName a => a -> Diagram B
notGate name = dualInput name ||| triangle 1 # rotate (-1/4 @@ turn) ||| smallNot ||| mkCon (name, "out")

nothing :: Diagram B
nothing = pointDiagram $ mkP2 0 0

mkCon :: IsName a => a -> Diagram B
mkCon name = nothing # named name

con :: IsName a => a -> Diagram B
con name = circle 0.05 # fc black <> mkCon name

putAt :: IsName a => Diagram B -> a -> Diagram B -> Diagram B
putAt what name = withName name $ \b d -> moveTo (location b) what <> d

test = (labeled "m" (machine "sr" ["S", "R"] ["Q", "Q'"] "SR"
     ||| spacer
     ||| orGate "a"
     )
     ||| spacer
     ||| notGate "not"
     ||| machine "neg" [""] ["+", "-"] "±"
     ) # connect' headless ("sr", "out1") ("a", "in1")
       # putAt polyIn ("sr", "S")
       # putAt (con "split") ("a", "in1")
       # connect' headless "split" ("a", "in0")
       # connect' headless ("a", "out0") ("not", "in0")


rsDef :: Diagram B
rsDef = labeled "RS"
    $ ((norGate "norA" ||| inputWire ||| (con "feedA" === vspacer === mkCon "loopA") ||| inputWire ||| wireLabel "Q")
    === spacer
    === spacer
    === (norGate "norB" ||| inputWire ||| (mkCon "loopB" === vspacer === mkCon "feedB") # alignB)
    ) # connect' headless "feedA" "loopA"
      # connect' headless "feedB" "loopB"
      # putAt ((mkCon "inB" === vspacer) # alignB) ("norB", "in0")
      # connect' headless "loopA" "inB"
      # connect' headless "inB" ("norB", "in0")
      # putAt (vspacer === mkCon "inA") ("norA", "in1")
      # connect' headless "loopB" "inA"
      # connect' headless "inA" ("norA", "in1")

      # putAt ((inputWire <> wireLabel "R") # alignR) ("norA", "in0")
      # putAt ((inputWire <> wireLabel "S") # alignR) ("norB", "in1")

rsMachine :: IsName a => a -> Diagram B
rsMachine name = machine name ["R", "S"] ["Q"] "RS"

isMachine :: IsName a => a -> Diagram B
isMachine name = machine name ["I", "S"] ["Q"] "IS"

labeled :: String -> Diagram B -> Diagram B
labeled label d = ( d # center
                 <> rect (width d - 0.5) (height d + 0.25) # lw veryThick
                  ) === svspacer === text label # scale labelSize

headless = with & arrowHead .~ noHead

arr :: (IsName a, IsName b) => a -> b -> Diagram B -> Diagram B
arr = connect' headless

wireLabel :: String -> Diagram B
wireLabel s = text s # scale textSize # translate (r2 (0, 0.2))

labeledWire :: String -> Diagram B
labeledWire s = (wireLabel s <> inputWire) ||| mkCon s

moveDef :: Diagram B
moveDef = labeled "Mov" $ ( (labeledWire "A" === svspacer === split)
        ||| spacer
        ||| spacer
        ||| (andGate "top" === ssvspacer === andGate "bot")
          ) # putAt ((con "splitA" ||| inputWire) # alignR) ("top", "in0")
            # putAt ((mkCon "splitB" ||| inputWire) # alignR) ("bot", "in0")
            # putAt (inputWire ||| wireLabel "A+") ("top", "out0")
            # putAt (inputWire ||| wireLabel "A-") ("bot", "out0")
            # arr "A" "splitA"
            # arr "splitA" "splitB"
            # arr ("neg", "out0") ("top", "in1")
            # arr ("neg", "out1") ("bot", "in1")
  where
    split = wireLabel "W" <> machine "neg" [""] ["+", "-"] "±"

blackBox :: IsName a => a -> String -> Diagram B
blackBox name = machine name [""] [""] # bold

polyMachDef :: Diagram B
polyMachDef = labeled "Poly[M]"
                $ machine "move" ["A", "W"] ["A+", "A-"] "Mov"
                # putAt (polyIn ||| blackBox "m1" "M" & alignL) ("move", "out0")
                # putAt (polyIn ||| blackBox "m2" "M" & alignL) ("move", "out1")
                # putAt (polyIn ||| wireLabel "I" & alignR) ("move", "in0")
                # putAt (wireLabel "W" & alignR) ("move", "in1")
                # putAt (polyIn ||| inputWire ||| wireLabel "M+" & alignL) ("m1", "out0")
                # putAt (polyIn ||| inputWire ||| wireLabel "M-" & alignL) ("m2", "out0")

main :: IO ()
main = mainWith $ ((polyMachDef === vspacer === moveDef === vspacer === rsDef) # pad 1.2 # scale 50 :: Diagram B)


