module Take2.Computer.Math where

import           Prelude hiding ((.), id, sum)
import           Circuitry.Machinery
import qualified Circus.Types as Y


everyPair
    :: (OkCircuit a, OkCircuit b, OkCircuit c)
    => Circuit (a, (b, c))
               ((a, b), ((a, c), (b, c)))
everyPair = (reassoc >>> fst')
       &&& ((second' swap >>> reassoc >>> fst') &&& snd')


cout :: Circuit (Bool, (Bool, Bool)) Bool
cout = everyPair
   >>> andGate *** (andGate *** andGate)
   >>> ((reassoc >>> fst') &&& snd')
   >>> orGate *** orGate
   >>> orGate


sum :: Circuit (Bool, (Bool, Bool)) Bool
sum = second' xorGate >>> xorGate


-- input: A B Cin
-- output: S Cout
add2 :: Circuit (Bool, (Bool, Bool)) (Bool, Bool)
add2 = copy >>> sum *** cout


addN :: (SeparatePorts a, Numeric a, OkCircuit a) => Circuit (a, a) (a, Bool)
addN = diagrammed (binaryGateDiagram Y.CellAdd)
     $ shortcircuit (uncurry addNumeric)
     $ serial *** serial
   >>> zipVC
   >>> create
   >>> second' (constC False)
   >>> mapFoldVC (reassoc' >>> add2)
   >>> first' unsafeParse


shiftL :: forall a. (1 <= SizeOf a, Embed a, Numeric a) => Circuit a a
shiftL = unsafeReinterpret @_ @(Vec (SizeOf a - 1) Bool, Bool)
     >>> fst'
     >>> create
     >>> swap
     >>> first' (constC $ zero @Bool)
     >>> unsafeReinterpret


shiftR :: forall a. (1 <= SizeOf a, Embed a, Numeric a) => Circuit a a
shiftR = serial
     >>> unconsC @(SizeOf a - 1)
     >>> snd'
     >>> create
     >>> second' (constC $ zero @Bool)
     >>> unsafeReinterpret


ashiftR :: forall a. (2 <= SizeOf a, Embed a, Numeric a) => Circuit a a
ashiftR = serial
     >>> unconsC @(SizeOf a - 1)
     >>> snd'
     >>> unsafeReinterpret @_ @(Vec (SizeOf a - 2) Bool, Bool)
     >>> second' copy
     >>> unsafeReinterpret
