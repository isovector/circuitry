{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Lens hiding ((#), at)
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude
import Diagrams.TwoD.Shapes
import Diagrams.Backend.Canvas.CmdLine

andGate :: Diagram B
andGate = (input (-1) <> input 1)
       ||| roundedRect' 1.2 1 (with & radiusBR .~ 0.5
                                    & radiusTR .~ 0.5
                                    )
       ||| line # named "and-out"
  where
    line = fromOffsets [unitX] # scale 0.5
    input d = line # translate (r2 (0, spacing * d)) # named ("and-in" ++ show d)
    spacing = 0.25

-- TODO(sandy): fix this cause it's shitty
orGate :: Diagram B
orGate = roundedRect' 1.2 1 (with & radiusBR .~ 0.5
                                  & radiusTR .~ 0.5
                                  & radiusBL .~ -0.3
                                  & radiusTL .~ -0.3
                                  )

test = andGate # scale 50 # connectPerim' arrowStyle2 "aabc" "and-out" (4/12 @@ turn) (2/12 @@ turn)
  where
    shaft' = arc xDir (-2.7/5 @@ turn)
    arrowStyle2 = (with  & arrowHead   .~ spike
                     & arrowShaft  .~ shaft' & arrowTail .~ lineTail
                     & tailTexture .~ solid black & lengths .~ normal)


main :: IO ()
main = mainWith $ (test :: Diagram B)


