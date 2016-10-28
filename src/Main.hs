{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Data.Typeable
import Control.Arrow (first)
import Control.Monad (zipWithM_)
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude hiding (anon)
import Diagrams.TwoD.Shapes
import Diagrams.TwoD.Layout.Constrained ((=.=))

import Circuitry
import Circuitry.Backend
import Circuitry.Gates
import Circuitry.Misc
import Circuitry.Types

test :: Diagram B
test = runCircuit $ do
    [and1, or1] <- liftDias [andGate, orGate]
    withPort or1 (In 0) $ \p1 -> do
        withPort and1 (Out 0) $ \p2 -> leftOf p2 p1
        anon con $ \(s, p2) -> do
            liftCircuit $ p1 =.= p2
            arr (s, Split) (or1, In 1)
        withPort and1 (In 1) $ \p2 ->
            anon bend $ \(b1, b1p) ->
            anon bend $ \(b2, b2p) -> do
                above p2 b1p
                above p1 b2p
                leftOf b1p b2p
                spaceV 0.25 or1 b1
                arr (b1, Split) (b2, Split)
                arr (b1, Split) (and1, In 1)
                arr (b2, Split) (or1, In 1)
    withPort or1 (In 1) $ \p1 -> do
        anon con $ \(s, p2) -> do
            liftCircuit $ p1 =.= p2

    arr (and1, Out 0) (or1, In 0)
    spaceH 1 and1 or1
    return ()

labeled :: String -> Diagram B -> Diagram B
labeled label d = ( d # center
                 <> rect (width d - 0.5) (height d + 0.25) # lw veryThick
                  ) === svspacer === text label # scale labelSize

wireLabel :: String -> Diagram B
wireLabel s = text s # scale textSize # translate (r2 (0, 0.2))

labeledWire :: String -> Diagram B
labeledWire s = (wireLabel s <> inputWire) ||| mkCon s

main :: IO ()
main = mainWith $ (test # pad 1.2 # scale 50 :: Diagram B)

