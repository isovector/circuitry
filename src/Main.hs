{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Lens hiding ((#), at)
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude
import Diagrams.TwoD.Shapes
import Diagrams.Backend.Canvas.CmdLine

dualInput :: IsName a => a -> Diagram B
dualInput name = input 1 "in1" <> input (-1) "in2"
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
           ||| mkCon (name, "out")

spacer :: Diagram B
spacer = rect 0.5 0.5 # lc white

machine :: IsName a => a -> [String] -> [String] -> String -> Diagram B
machine name ins outs labelText = inputStack ||| (rect width height <> inLabels <> outLabels <> label) ||| outputStack
  where
    vspacing = 1.9
    hspacing = width / 2 - textSize
    labelSize = 0.3
    textSize = 0.2
    width = (fromIntegral ( maximum (fmap length ins)
                          + maximum (fmap length outs)) * textSize)
          + (fromIntegral (length labelText) * labelSize) + 0.5
    label = text labelText # scale labelSize
    height = max (heightOf outs) (heightOf ins) + 0.3
    -- TODO(sandy): this is negative. wtf?
    heightOf ls = -vspacing * fromIntegral (length ls - 1) / 2
    stack as = foldl (\b a -> b # translate (r2 (0, vspacing)) <> a) nothing as
    inputStack = stack (fmap (\a -> mkCon (name, a) ||| inputLine) ins) # translate (r2 (0, heightOf ins)) # scaleY textSize
    outputStack = stack (fmap (\a -> mkCon (name, a)) outs) # translate (r2 (0, heightOf outs)) # scaleY textSize
    textStack ls = stack (fmap text ls) # translate (r2 (0, heightOf ls)) # scale textSize
    inLabels  = textStack ins # translate (r2 (-hspacing, 0))
    outLabels = textStack outs # translate (r2 (hspacing, 0))

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

putAt :: IsName a => Diagram B -> a -> Diagram B -> Diagram B
putAt what name = withName name $ \b d -> moveTo (location b) what <> d

test = (machine "sr" ["S", "R", "W"] ["Q", "Q'", "b", "a"] "SR"
     ||| polyIn
     ||| spacer
     ||| andGate "a"
     ||| notGate "not"
     ||| andGate "b") # connect' headless ("sr", "Q") ("a", "in1")
                      # putAt polyIn ("sr", "S")

headless = with & arrowHead .~ noHead


main :: IO ()
main = mainWith $ (test # scale 50 :: Diagram B)


