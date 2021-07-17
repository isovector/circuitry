module Take2.Computer.Addressed where

import Prelude hiding ((.), id, sum)
import Circuitry.Machinery

------------------------------------------------------------------------------
-- | Duplicate the given circuit @2^n@ times, and put a decoder on the address.
-- Each circuit gets a 'Bool' corresponding to whether or not they were the one
-- decoded. Combine all back together with a bus.
addressed
    :: forall n a b
     . (Embed a, Embed b, KnownNat n)
    => Circuit (a, Bool) b
    -> Circuit (Addr n, a) b
addressed c = decode *** cloneV
          >>> zipVC
          >>> mapV ( swap
                 >>> second' copy
                 >>> reassoc
                 >>> first' (c >>> serial)
                 >>> tribufAll
                   )
          >>> transposeV
          >>> mapV unsafeShort
          >>> unsafeParse


decode :: KnownNat n => Circuit (Addr n) (Vec (2 ^ n) Bool)
decode = component "decode" $ unsafeReinterpret >>> crossV andGate

