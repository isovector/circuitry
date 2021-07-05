module Take2.Computer.Memory where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Simple
import Take2.Machinery


hold :: Circuit Bool Bool
hold = fixC False $ orGate >>> copy


-- input: R S
rsLatch :: Circuit (Bool, Bool) Bool
rsLatch = component "rs"
         $ fixC False
         $ reassoc'
      >>> second' norGate
      >>> norGate
      >>> copy


-- input: S V
snap :: Circuit (Bool, Bool) Bool
snap = component "snap"
     $ second' (split >>> swap)
   >>> distribP
   >>> both andGate
   >>> rsLatch


snapN :: forall a. (Nameable a, OkCircuit a, SeparatePorts a) => Circuit (Bool, a) (Vec (SizeOf a) Bool)
snapN = component ("snap " <> nameOf @a)
      $ second' serial
    >>> distribV
    >>> mapV snap

