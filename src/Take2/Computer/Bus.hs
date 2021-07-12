{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Take2.Computer.Bus where

import Prelude hiding ((.), id, sum)
import Take2.Machinery
import Take2.Computer.Memory
import Take2.Computer.ALU
import Type.Reflection


data BusCommand n word
  = BusMemory (MemoryCommand n word)
  | BusAlu    (AluCommand word)
  | BusROM    (Addr n)
  deriving stock Generic
  deriving anyclass Embed

bus
    :: forall n word
     . ( 2 <= SizeOf word
       , Embed word
       , KnownNat n
       , Nameable word
       , Numeric word
       , SeparatePorts word
       , Show word
       , Typeable word
       )
    => Vec (2 ^ n) word
    -> Circuit (BusCommand n word)
               (Vec (SizeOf word) Bool)
bus rom =
  elim_
       $ #_BusMemory :-> fst' >>> memoryCell @n @word
   :+| ( #_BusAlu    :-> fst' >>> alu @word
     :+| #_BusROM    :-> fst' >>> mkRom rom >>> serial
       )

