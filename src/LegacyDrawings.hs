

polyIn :: Diagram B
polyIn = pline 3 <> pline 2 <> pline 1
  where
    pline h = fromOffsets [unitY] # scale (0.1*h) # translate (r2 ((-0.05) * h, (-0.1 / 2) * h))

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

polyMachDef :: Diagram B
polyMachDef = labeled "Poly[M]"
                $ machine "move" ["A", "W"] ["A+", "A-"] "Mov"
                # putAt (polyIn ||| blackBox "m1" "M" & alignL) ("move", "out0")
                # putAt (polyIn ||| blackBox "m2" "M" & alignL) ("move", "out1")
                # putAt (polyIn ||| wireLabel "I" & alignR) ("move", "in0")
                # putAt (wireLabel "W" & alignR) ("move", "in1")
                # putAt (polyIn ||| inputWire ||| wireLabel "M+" & alignL) ("m1", "out0")
                # putAt (polyIn ||| inputWire ||| wireLabel "M-" & alignL) ("m2", "out0")

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
