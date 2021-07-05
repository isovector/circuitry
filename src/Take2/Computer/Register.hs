{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}

module Take2.Computer.Register where

import Data.Typeable (Typeable)
import Prelude hiding ((.), id, sum)
import Take2.Computer.Addressed
import Take2.Computer.Math (addN)
import Take2.Computer.Memory
import Take2.Computer.Simple
import Take2.Machinery
import Take2.Product
import GHC.TypeLits.Extra (Max)


data Register
  = NO_REGISTER
  | PC
  | SP
  | X
  | Y
  | A
  | FLAGS
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (Embed)

instance Arbitrary Register where
  arbitrary = oneof $ fmap pure [NO_REGISTER, PC, X, Y, A, FLAGS]


data Flags = Flags
  { f_neg      :: Bool
  , f_overflow :: Bool
  , f_zero     :: Bool
  , f_carry    :: Bool
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass Embed

data Registers pc sp word = Registers
  { reg_PC    :: pc
  , reg_SP    :: sp
  , reg_X     :: word
  , reg_Y     :: word
  , reg_A     :: word
  , reg_flags :: Flags
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass Embed


-- registerStore
--     :: (Embed a, Nameable a, SeparatePorts a)
--     => Circuit (Register, a) (Registers a)
-- registerStore = first' unsafeReinterpret >>> registerStoreImpl


boolToRW :: Circuit Bool RW
boolToRW = unsafeReinterpret


registerStore
    :: forall pc sp word
     . ( Embed pc
       , Nameable pc
       , SeparatePorts pc
       , Embed sp
       , Nameable sp
       , SeparatePorts sp
       , Embed word
       , Nameable word
       , SeparatePorts word
       , SizeOf sp <= SizeOf pc
       , SizeOf word <= SizeOf pc
       , SizeOf Flags <= SizeOf pc
       )
    => Circuit (Register, Vec (SizeOf pc) Bool)
               (Registers pc sp word)
registerStore
    = sequenceMetaV (fmap (uncurry when')
        ( (PC,     snapN')
       :> (SP,     second' (separate @(SizeOf sp) >>> fst') >>> snapN' >>> pad False)
       :> (X ,     second' (separate @(SizeOf word) >>> fst') >>> snapN' >>> pad False)
       :> (Y ,     second' (separate @(SizeOf word) >>> fst') >>> snapN' >>> pad False)
       :> (A ,     second' (separate @(SizeOf word) >>> fst') >>> snapN' >>> pad False)
       :> (FLAGS , second' (separate @(SizeOf Flags) >>> fst') >>> snapN' >>> pad False)
       :> Nil
        ))
  >>> foldRegisterRecord


snapN' :: (Embed c, Nameable c, SeparatePorts c) => Circuit (Bool, c) (Vec (SizeOf c) Bool)
snapN' = first' boolToRW >>> snapN


foldRegisterRecord
    :: forall pc sp word
     . ( Embed pc, Embed sp, Embed word
       , SizeOf sp <= SizeOf pc
       , SizeOf word <= SizeOf pc
       , SizeOf Flags <= SizeOf pc
       )
    => Circuit (Vec 6 (Vec (SizeOf pc) Bool)) (Registers pc sp word)
foldRegisterRecord
    = unconsC
  >>> second'
      ( unconsC
    >>> ( separate @(SizeOf sp) >>> fst')
    *** ( unconsC
      >>> (separate @(SizeOf word) >>> fst')
      *** ( unconsC
        >>> (separate @(SizeOf word) >>> fst')
        *** ( unconsC
          >>> (separate @(SizeOf word) >>> fst')
          *** (lower >>> separate @(SizeOf Flags) >>> fst')
            )
          )
        )
      )
  >>> unsafeReinterpret




--       decode *** cloneV
--   >>> zipVC
--   >>> mapV (first' unsafeReinterpret >>> snapN @(a))
--   >>> unsafeReinterpret @_ @(a, Vec 3 (a))
--   >>> snd'
--   >>> unsafeReinterpret

data Op
  = JMP
  | MOV
  | INC
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed

-- cpu
--     :: forall a
--     . (2 <= SizeOf a, Typeable a, Embed a, Nameable a, SeparatePorts a, Num a, Show a, Numeric a)
--     => Circuit (Op, (a, a)) (Registers a)
-- cpu = fixC (Registers @a 0 0 0)
--     $  reassoc'
--   >>> branch
--         ( (JMP, fst'
--             >>> fst'
--             >>> intro PC
--             >>> swap
--             >>> serial
--           )
--        :> (MOV, fst'
--             >>> first' ( unsafeReinterpret @_ @(Register, Vec (SizeOf a - SizeOf Register) Bool)
--                      >>> fst'
--                        )
--             >>> serial
--           )
--        :> (INC, snd'
--             >>> proj #reg_X
--             >>> intro 1
--             >>> addN
--             >>> fst'
--             >>> intro OP1
--             >>> swap
--             >>> serial
--           )
--        :> Nil
--         )
--   >>> unsafeParse @(Register, a)
--   >>> registerStore
--   >>> copy


