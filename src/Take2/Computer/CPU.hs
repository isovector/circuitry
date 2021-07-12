{-# LANGUAGE NoMonomorphismRestriction            #-}
{-# LANGUAGE UndecidableInstances                 #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20000 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Take2.Computer.CPU where

import qualified Clash.Sized.Vector as V
import           Data.Typeable (Typeable)
import           GHC.TypeLits.Extra (Max)
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.ALU
import           Take2.Computer.Bus
import           Take2.Computer.Memory
import           Take2.Computer.Register
import           Take2.Machinery
import           Take2.Primitives (Dict(Dict))
import           Unsafe.Coerce (unsafeCoerce)


data Instruction = Instruction Bool
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass Embed

data Step
  = Fetch
  | IncPC   Instruction
  | Execute Instruction
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass Embed


cpu
    :: forall pc sp word n
     . ( Embed pc
       , Embed sp
       , Embed word
       , Typeable pc
       , Typeable sp
       , Typeable word
       , SeparatePorts pc
       , SeparatePorts sp
       , SeparatePorts word
       , 2 <= SizeOf word
       , Nameable word
       , Nameable pc
       , Nameable sp
       , Numeric word
       , Show word
       , KnownNat n
       , SizeOf (MemoryCommand n word) <= SizeOf (BusCommand n word)
       , (1 + SizeOf pc) <= (1 + (n + SizeOf word))
       )
    => Vec (2 ^ n) word
    -> Circuit () (Registers pc sp word)
cpu rom
    = registers @pc @sp @word
    $ fixC Fetch
    $ first' snd'
  >>> swap
  >>> first' copy
  >>> reassoc'
  >>> second' (
        ( elim $ #_Fetch
                 :-> snd'
                 >>> copy
                 >>> second' fetch
           :+| ( #_IncPC :-> undefined
              :+| undefined
               )
        )
    >>> second' (bus @n @word rom)
              )
  >>> (second' fst' >>> swap >>> first' copy)

fetch
    :: forall pc sp n word
     . ( Embed pc
       , KnownNat n, Embed word, Embed sp
       , SizeOf (MemoryCommand n word) <= SizeOf (BusCommand n word)
       , (1 + SizeOf pc) <= (1 + (n + SizeOf word))
       , Typeable pc
       , Typeable sp
       , Typeable word
       , SeparatePorts pc
       , SeparatePorts sp
       , SeparatePorts word
       )
    => Circuit (Registers pc sp word) (BusCommand n word)
fetch = proj #reg_PC
    >>> intro R
    >>> swap
    >>> serial
    >>> pad False
    >>> unsafeParse @(MemoryCommand n word)
    >>> case idiotGhcProof
               @(n + SizeOf word)
               @(Max (Max (((SizeOf word + SizeOf word) + 1) + 1) ((SizeOf word + 1) + 1) + 1) n)
               of
           Dict -> inj #_BusMemory


idiotGhcProof :: forall a b. Dict (Max (1 + a) (b + 1) ~ (Max a b + 1))
idiotGhcProof = unsafeCoerce $ Dict @(0 ~ 0)

-- test :: Circuit (MemoryCommand n word) (BusCommand n word)
-- test = inj #_BusMemory

-- fetch
--     :: ( Embed pc
--        , Embed sp
--        , Embed word
--        , SeparatePorts pc
--        , SeparatePorts sp
--        , SeparatePorts word
--        , Typeable pc
--        , Typeable sp
--        , Typeable word
--        )
--     => Circuit (Registers pc sp word) (Registers pc sp word, Step)
-- fetch = copy
--     >>> first' (proj #reg_PC)
--     >>> _

