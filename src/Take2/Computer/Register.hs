{-# LANGUAGE UndecidableInstances #-}

module Take2.Computer.Register where

import Data.Typeable (Typeable)
import Prelude hiding ((.), id, sum)
import Take2.Computer.Addressed
import Take2.Computer.Math (addN)
import Take2.Computer.Memory
import Take2.Computer.Simple
import Take2.Machinery
import Take2.Product


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

data Op
  = JMP
  | MOV
  | INC
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed

cpu
    :: forall a
    . (2 <= SizeOf a, Typeable a, Embed a, Nameable a, SeparatePorts a, Num a, Show a, Numeric a)
    => Circuit (Op, (a, a)) (Registers a)
cpu = fixC (Registers @a 0 0 0)
    $  reassoc'
  >>> branch
        ( (JMP, fst'
            >>> fst'
            >>> intro PC
            >>> swap
            >>> serial
          )
       :> (MOV, fst'
            >>> first' ( unsafeReinterpret @_ @(Register, Vec (SizeOf a - SizeOf Register) Bool)
                     >>> fst'
                       )
            >>> serial
          )
       :> (INC, snd'
            >>> proj #reg_OP1
            >>> intro 1
            >>> addN
            >>> fst'
            >>> intro OP1
            >>> swap
            >>> serial
          )
       :> Nil
        )
  >>> unsafeParse @(Register, a)
  >>> registerStore
  >>> copy


