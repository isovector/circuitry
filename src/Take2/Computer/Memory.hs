{-# LANGUAGE UndecidableInstances #-}
module Take2.Computer.Memory where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Simple
import Take2.Computer.Addressed
import Take2.Machinery
import Take2.Product (proj)
import Test.QuickCheck.Arbitrary.Generic (genericArbitrary, genericShrink)
import Data.Typeable (Typeable)


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
  deriving (Embed, Arbitrary) via (EmbededEnum RW)

maybeC :: Embed a => Circuit (Maybe a) (Either () a)
maybeC = unsafeReinterpret

maybeC' :: Embed a => Circuit (Either () a) (Maybe a)
maybeC' = unsafeReinterpret


data MemoryCommand f n a = MemoryCommand
  { mc_rw   :: f RW
  , mc_addr :: Addr n
  , mc_data :: a
  }
  deriving stock (Generic)

deriving anyclass instance (KnownNat n, Embed a, Embed (f RW))  => Embed (MemoryCommand f n a)

instance (KnownNat n, Arbitrary a, Arbitrary (f RW)) => Arbitrary (MemoryCommand f n a) where
  arbitrary = genericArbitrary
  shrink = genericShrink


unpackMemoryCommand :: (Embed a, KnownNat n, SeparatePorts (f RW), Typeable f, SeparatePorts a, Typeable a, Embed (f RW)) => Circuit (MemoryCommand f n a) ((Addr n, f RW), a)
unpackMemoryCommand
    = copy
  >>> (copy >>> proj #mc_addr *** proj #mc_rw)
  *** proj #mc_data


memoryCell
    :: forall n a
     . (Nameable a, SeparatePorts a, KnownNat n, Embed a, Typeable a)
    => Circuit (MemoryCommand Maybe n a) (Vec (SizeOf a) Bool)
memoryCell
    = unpackMemoryCommand
  >>> first' ( second' ( maybeC
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

