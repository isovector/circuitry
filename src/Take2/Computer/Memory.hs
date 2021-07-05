module Take2.Computer.Memory where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Simple
import Take2.Computer.Addressed
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
snap :: Circuit (RW, Bool) Bool
snap = component "snap"
     $ unsafeReinterpret @_ @Bool *** (split >>> swap)
   >>> distribP
   >>> both andGate
   >>> rsLatch


snapN :: forall a. (Nameable a, OkCircuit a, SeparatePorts a) => Circuit (RW, a) (Vec (SizeOf a) Bool)
snapN = component ("snap " <> nameOf @a)
      $ second' serial
    >>> distribV
    >>> mapV snap

data RW = R | W
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed

maybeC :: Embed a => Circuit (Maybe a) (Either () a)
maybeC = unsafeReinterpret

maybeC' :: Embed a => Circuit (Either () a) (Maybe a)
maybeC' = unsafeReinterpret

memoryCell
    :: forall n a
     . (Nameable a, SeparatePorts a, KnownNat n, Embed a)
    => Circuit ((Addr n, Maybe RW), a) (Vec (SizeOf a) Bool)
memoryCell
    = first' ( second' ( maybeC
                     >>> unsafeReinterpret @_ @(Bool, RW)
                     >>> second' copy
                     >>> reassoc
                     >>> first' ( second' ( unsafeReinterpret @_ @Bool >>> notGate)
                              >>> andGate
                                )
                       )
           >>> swap
           >>> reassoc'
             )
  >>> reassoc'
  >>> second' ( first' swap
            >>> reassoc'
            >>> addressed ( first' swap
                        >>> reassoc'
                        >>> second' (first' unsafeReinterpret >>> andGate >>> unsafeReinterpret @_ @RW)
                        >>> swap
                        >>> snapN
                          )
              )
  >>> swap
  >>> tribufAll

