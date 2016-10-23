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
    input d n = (mkCon (name, n) ||| inputLine) # translate (r2 (0, spacing * d))
    spacing = 0.25

inputLine :: Diagram B
inputLine = fromOffsets [unitX] # scale 0.5

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
machine name ins outs labelText = inputNumStack ||| inputStack ||| (rect width height <> inLabels <> outLabels <> label) ||| outputStack ||| outputNumStack
  where
    vspacing = 2.5
    hspacing = width / 2 - textSize
    width = (fromIntegral ( maximum (fmap length ins)
                          + maximum (fmap length outs)) * textSize)
          + (fromIntegral (length labelText) * labelSize) + 0.5
    label = text labelText # scale labelSize
    height = min (heightOf outs) (heightOf ins)
    -- TODO(sandy): this is negative. wtf?
    heightOf ls = -vspacing * fromIntegral (length ls - 1) / 2
    stack as = foldl (\b a -> b # translate (r2 (0, vspacing)) <> a) nothing as

    objStack as f = stack (fmap f as) # translate (r2 (0, heightOf as)) # scaleY textSize

    inputNumStack  = objStack (renumber ins) $ \a -> mkCon (name, "in" ++ a)
    inputStack     = objStack ins $ \a -> mkCon (name, a) ||| inputLine
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
rsDef = ((norGate "norA" ||| inputLine ||| (con "feedA" === vspacer === mkCon "loopA") ||| inputLine ||| wireLabel "Q")
    === spacer
    === spacer
    === (norGate "norB" ||| inputLine ||| (mkCon "loopB" === vspacer === mkCon "feedB") # alignB)
    ) # connect' headless "feedA" "loopA"
      # connect' headless "feedB" "loopB"
      # putAt ((mkCon "inB" === vspacer) # alignB) ("norB", "in0")
      # connect' headless "loopA" "inB"
      # connect' headless "inB" ("norB", "in0")
      # putAt (vspacer === mkCon "inA") ("norA", "in1")
      # connect' headless "loopB" "inA"
      # connect' headless "inA" ("norA", "in1")

      # putAt ((inputLine <> wireLabel "R") # alignR) ("norA", "in0")
      # putAt ((inputLine <> wireLabel "S") # alignR) ("norB", "in1")

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
labeledWire s = (wireLabel s <> inputLine) ||| mkCon s

moveDef :: Diagram B
moveDef = labeled "Mov" $ ( (labeledWire "A" === svspacer === split)
        ||| spacer
        ||| spacer
        ||| (andGate "top" === ssvspacer === andGate "bot")
          ) # putAt ((con "splitA" ||| inputLine) # alignR) ("top", "in0")
            # putAt ((mkCon "splitB" ||| inputLine) # alignR) ("bot", "in0")
            # putAt (inputLine ||| wireLabel "A+") ("top", "out0")
            # putAt (inputLine ||| wireLabel "A-") ("bot", "out0")
            # arr "A" "splitA"
            # arr "splitA" "splitB"
            # arr ("neg", "out0") ("top", "in1")
            # arr ("neg", "out1") ("bot", "in1")
  where
    split = wireLabel "W" <> machine "neg" [""] ["+", "-"] "±"

main :: IO ()
main = mainWith $ (moveDef # pad 2 # scale 50 :: Diagram B)


