module Take2.Computer.Examples where

import Prelude hiding ((.), id, sum)
import Circuitry.Machinery
import Take2.Computer.Math


tickTock :: Circuit () Bool
tickTock = fixC False $ snd' >>> copy >>> second' notGate


clock
    :: forall a. (Show a, SeparatePorts a, Embed a, OkCircuit a, Numeric a)
    => Circuit () a
clock = fixC (zero @a)
      $ first' (constC one)
    >>> swap
    >>> first' copy
    >>> reassoc'
    >>> second' (addN >>> fst')

