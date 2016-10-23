{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Lens hiding ((#), at)
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude
import Diagrams.TwoD.Shapes
import Diagrams.Backend.Canvas.CmdLine

andGate :: IsName a => a -> Diagram B
andGate name = (input (-1) "in1" <> input 1 "in2")
       ||| roundedRect' 1.2 1 (with & radiusBR .~ 0.5
                                    & radiusTR .~ 0.5
                                    )
       ||| line # named (name, "out") # rotate (1/2 @@ turn)
  where
    line = fromOffsets [unitX] # scale 0.5
    input d n = line # named (name, n) # translate (r2 (0, spacing * d))
    spacing = 0.25

-- TODO(sandy): fix this cause it's shitty
orGate :: Diagram B
orGate = roundedRect' 1.2 1 (with & radiusBR .~ 0.5
                                  & radiusTR .~ 0.5
                                  & radiusBL .~ -0.3
                                  & radiusTL .~ -0.3
                                  )

test = (andGate "a" ||| andGate "b") # connectPerim' arrowStyle2 ("b", "out") ("a", "in1") (4/12 @@ turn) (2/12 @@ turn)
  where
    shaft' = arc xDir (-2.7/5 @@ turn)
    arrowStyle2 = (with  & arrowHead   .~ spike
                     & arrowShaft  .~ shaft' & arrowTail .~ lineTail
                     & tailTexture .~ solid black & lengths .~ normal)


main :: IO ()
main = mainWith $ (test # scale 50 :: Diagram B)


