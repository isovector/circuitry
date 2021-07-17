{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Take2.Computer.Bus where

import Prelude hiding ((.), id, sum)
import Circuitry.Machinery
import Take2.Computer.Memory
import Take2.Computer.ALU
import Type.Reflection


data BusCommand n word
  = BusMemory (MemoryCommand n word)
  | BusAlu    (AluCommand word)
  | BusROM    (Addr n)
  deriving stock (Show, Generic)
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
  elim_ $ foldElim
       $ #_BusMemory :=> memoryCell @n @word
     :+| #_BusAlu :=> alu @word
     :+| #_BusROM :=> mkRom rom >>> serial
     :+| End

