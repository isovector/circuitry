{-# LANGUAGE UndecidableInstances #-}

module Take2.Computer.Register where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Addressed
import Take2.Machinery
import Take2.Product
import Take2.Computer.Memory

data Register
  = NO_REGISTER
  | PC
  | OP1
  | OP2
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (Embed)

instance Arbitrary Register where
  arbitrary = oneof $ fmap pure [NO_REGISTER, PC, OP1, OP2]


data Registers a = Registers
  { reg_PC :: a
  , reg_OP1 :: a
  , reg_OP2 :: a
  -- , reg_OP3 :: a
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass Embed

deriving anyclass instance Embed a => Proj "reg_PC" a (Registers a)
deriving anyclass instance Embed a => Proj "reg_OP1" a (Registers a)
deriving anyclass instance Embed a => Proj "reg_OP2" a (Registers a)


registerStore
    :: (Embed a, Nameable a, SeparatePorts a)
    => Circuit (Register, a) (Registers a)
registerStore = first' unsafeReinterpret >>> registerStoreImpl


registerStoreImpl
    :: forall a. (Embed a, Nameable a, SeparatePorts a )
    => Circuit (Addr 2, a) (Registers a)
registerStoreImpl
    = decode *** cloneV
  >>> zipVC
  >>> mapV (first' unsafeReinterpret >>> snapN @(a))
  >>> unsafeReinterpret @_ @(a, Vec 3 (a))
  >>> snd'
  >>> unsafeReinterpret

