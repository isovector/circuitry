{-# LANGUAGE UndecidableInstances #-}

module Take2.Computer.Register where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Addressed
import Take2.Machinery
import Take2.Product
import Take2.Computer.Memory
import Take2.Computer.Simple hiding (when, branch)
import Take2.Primitives (constantName)
import Data.Typeable (Typeable)
import Take2.Computer.Math (addN)

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

data Op
  = JMP
  | MOV
  | INC
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed

when
    :: (1 <= SizeOf k, Embed k, Embed r, Show k, SeparatePorts a, Embed a)
    => Circuit a k
    -> k
    -> Circuit a r
    -> Circuit a (Vec (SizeOf r) Bool)
when get_k k c = interface' diagrammed (fmap (mappend "case ") $ constantName k)
           (copy >>> first' (get_k >>> intro k >>> eq))
       >>> ifOrEmpty c


branch
    :: forall a k n cases
     . ( 1 <= cases
       , 1 <= SizeOf k
       , Embed k
       , KnownNat n
       , Show k
       , KnownNat cases
       , SeparatePorts a
       , Embed a)
    => Circuit a k
    -> Vec cases (k, Circuit a (Vec n Bool))
    -> Circuit a (Vec n Bool)
branch get_k vs = sequenceMetaV (fmap (uncurry $ when get_k) vs) >>> pointwiseOr @cases

cpu
    :: forall a
    . (2 <= SizeOf a, Typeable a, Embed a, Nameable a, SeparatePorts a, Num a, Show a, Numeric a)
    => Circuit (Op, (a, a)) (Registers a)
cpu = fixC (Registers @a 0 0 0)
    $ branch (fst' >>> fst')
        ( (JMP, fst'
            >>> snd'
            >>> fst'
            >>> intro PC
            >>> swap
            >>> serial
          )
       :> (MOV, fst'
            >>> snd'
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


