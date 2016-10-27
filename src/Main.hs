{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Monad (zipWithM_)
import Control.Lens hiding ((#), at)
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude
import Diagrams.TwoD.Shapes

import Gates
import Machinery
import Misc
import Backend
import DSL
import Types

test :: Diagram B
test = runDSL $ do
    and1 <- liftDia andGate
    or1  <- liftDia orGate
    withPort and1 (Out 0)
        $ \p1 -> withPort or1 (In 0)
        $ \p2 -> leftOf p1 p2

    spaceH and1 or1 2

    return ()

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

main :: IO ()
main = mainWith $ (test # pad 1.2 # scale 50 :: Diagram B)

