{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Take2.Computer.Bus where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Simple
import Take2.Computer.Addressed
import Take2.Machinery
import Take2.Computer.Memory
import Take2.Computer.ALU
import Data.Typeable (Typeable)


data BusCommand n word
  = BusMemory (MemoryCommand n word)
  | BusAlu    (AluCommand word)
  deriving stock Generic
  deriving anyclass Embed

bus
    :: forall n word
     . ( Embed word
       , KnownNat n
       , Nameable word
       , SeparatePorts word
       , Typeable word
       , Numeric word
       , 2 <= SizeOf word
       , SizeOf (AluCommand word) <= SizeOf (BusCommand n word)
       , SizeOf (MemoryCommand n word) <= SizeOf (BusCommand n word)
       )
    => Circuit (BusCommand n word)
               (Vec (SizeOf word) Bool)
bus = elim $ Elim #_BusMemory (memoryCell @n @word)
         :+| Elim #_BusAlu (alu @word)

