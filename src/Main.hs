{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Monad (zipWithM_)
import Control.Lens hiding ((#), at)
import Data.Hashable
import Data.Maybe (fromJust)
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude
import Diagrams.TwoD.Shapes
import Diagrams.TwoD.Layout.Constrained

import Gates
import Machinery
import Misc
import Backend

polyIn :: Diagram B
polyIn = pline 3 <> pline 2 <> pline 1
  where
    pline h = fromOffsets [unitY] # scale (0.1*h) # translate (r2 ((-0.05) * h, (-0.1 / 2) * h))

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

originToName :: (Point V2 Double -> Point V2 Double) -> Named -> Diagram B -> Diagram B
originToName f (Named name) = withName name $ \b d -> d # moveOriginTo (f $ location b)

data Named where
  Named :: IsName a => a -> Named

polyMachDef :: Diagram B
polyMachDef = labeled "Poly[M]"
                $ machine "move" ["A", "W"] ["A+", "A-"] "Mov"
                # putAt (polyIn ||| blackBox "m1" "M" & alignL) ("move", "out0")
                # putAt (polyIn ||| blackBox "m2" "M" & alignL) ("move", "out1")
                # putAt (polyIn ||| wireLabel "I" & alignR) ("move", "in0")
                # putAt (wireLabel "W" & alignR) ("move", "in1")
                # putAt (polyIn ||| inputWire ||| wireLabel "M+" & alignL) ("m1", "out0")
                # putAt (polyIn ||| inputWire ||| wireLabel "M-" & alignL) ("m2", "out0")

findPort
  :: (IsName nm, Hashable n,
      Semigroup m, RealFrac n, Floating n) =>
     DiaID s -> nm -> Constrained s b n m (P2 (Expr s n))
findPort d name = newPointOn d (location . fromJust . lookupName name)

diagonalLayout :: Diagram B
diagonalLayout = labeled "Mov"
               $ layout constraints
               # arr "A" "splitA"
               # arr "splitA" "splitB"
               # arr "splitA" ("top", "in0")
               # arr "splitB" ("bot", "in0")
               # arr ("neg", "out0") "splitD"
               # arr ("neg", "out1") ("bot", "in1")
               # arr "splitD" "splitC"
               # arr "splitC" ("top", "in1")
  where
    constraints = do
      inA <- newDia $ labeledWire "A"
      inW <- newDia $ (wireLabel "W" <> machine "neg" [""] ["+", "-"] "±")
      and1 <- newDia $ (andGate "top" ||| inputWire ||| wireLabel "A+")
      and2 <- newDia $ (andGate "bot" ||| inputWire ||| wireLabel "A-")
      splitA <- newDia $ con "splitA"
      splitB <- newDia $ mkCon "splitB"

      splitC <- newDia $ mkCon "splitC"
      splitD <- newDia $ mkCon "splitD"

      and1In0 <- findPort and1 ("top", "in0")
      and1In1 <- findPort and1 ("top", "in1")
      and2In0 <- findPort and2 ("bot", "in0")

      constrainWith (hsep 2) [inA, splitA]

      sameX splitA splitB
      leftOf (centerOf splitB) and2In0

      leftOf (centerOf splitC) and1In1
      leftOf (centerOf inA) and1In0

      spaceH splitC and1 0.7
      leftOf (centerOf splitD) and2In0

      sameX splitC splitD

      -- sameY inA and1
      sameY inW and2
      sameX inA inW
      constrainWith (vsep 0.25) [and1, and2]

      spaceH inA and1 2.2

leftOf :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
        => P2 (Expr s n) -> P2 (Expr s n) -> Constrained s b n m ()
leftOf = constrainDir (direction (r2 (1, 0)))

above :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
      => P2 (Expr s n) -> P2 (Expr s n) -> Constrained s b n m ()
above = constrainDir (direction (r2 (0, 1)))

spaceH :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
        => DiaID s -> DiaID s-> n -> Constrained s b n m ()
spaceH a b s = do
  spacer <- newDia $ strut unitX # scaleX s # alignR
  constrainWith hcat [a, spacer]
  sameX b spacer

spaceV :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
        => DiaID s -> DiaID s -> n -> Constrained s b n m ()
spaceV a b s = do
  spacer <- newDia $ strut unitY # scaleY s # alignB
  constrainWith vcat [a, spacer]
  sameY b spacer

main :: IO ()
main = mainWith $ (diagonalLayout # pad 1.2 # scale 50 :: Diagram B)

