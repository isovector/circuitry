{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

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

spacer :: Diagram B
spacer = rect 0.5 0.5 # lc white

sspacer :: Diagram B
sspacer = rect 0.25 0.25 # lc white

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
con name = circle 0.05 # fc black # named name

putAt :: IsName a => Diagram B -> a -> Diagram B -> Diagram B
putAt what name = withName name $ \b d -> moveTo (location b) what <> d

test = (labeled "m" (machine "sr" ["S", "R"] ["Q", "Q'"] "SR"
     ||| spacer
     ||| andGate "a"
     )
     ||| spacer
     ||| notGate "not"
     ) # connect' headless ("sr", "out1") ("a", "in1")
       # putAt polyIn ("sr", "S")
       # putAt (con "split") ("a", "in1")
       # connect' headless "split" ("a", "in0")
       # connect' headless ("a", "out0") ("not", "in0")

labeled :: String -> Diagram B -> Diagram B
labeled label d = ( d # center # translate (r2 (-0.25, 0.125))
                 <> rect (width d) (height d + 0.25) # lw veryThick
                  ) === sspacer === text label # scale labelSize


headless = with & arrowHead .~ noHead


main :: IO ()
main = mainWith $ (test # scale 50 :: Diagram B)


