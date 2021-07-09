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
import GHC.TypeLits.Extra (Max)


data BusCommand n word
  = BusMemory (MemoryCommand n word)
  | BusAlu    (AluCommand word)
  | BusROM    (Addr n)
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
       , Show word
       , 2 <= SizeOf word
       , SizeOf (AluCommand word) <= SizeOf (BusCommand n word)
       , SizeOf (MemoryCommand n word) <= SizeOf (BusCommand n word)
       , SizeOf (Addr n) <= SizeOf (BusCommand n word)
       , n <= (Max (Max (((SizeOf word + SizeOf word) + 1) + 1)
                        ((SizeOf word + 1) + 1) + 1
                   ) n + 1)

        , ((Max (((SizeOf word + SizeOf word) + 1) + 1) ((SizeOf word + 1) + 1)
                          + 1)
                         <= (Max (Max (((SizeOf word + SizeOf word) + 1) + 1)
                                      ((SizeOf word + 1) + 1) + 1) n + 1))
       , ((Max
                            (Max
                               (((SizeOf word + SizeOf word) + 1) + 1) ((SizeOf word + 1) + 1)
                             + 1)
                            n
                          + 1)
                         <= (Max
                                             (1 + (n + SizeOf word))
                                             (Max
                                                (Max
                                                   (((SizeOf word + SizeOf word) + 1) + 1)
                                                   ((SizeOf word + 1) + 1)
                                                 + 1)
                                                n
                                              + 1)
                                           + 1))

       )
    => Vec (2 ^ n) word
    -> Circuit (BusCommand n word)
               (Vec (SizeOf word) Bool)
bus rom
  = elim $ #_BusMemory :-> memoryCell @n @word
         :+| ( #_BusAlu :-> alu @word
           :+| #_BusROM :-> mkRom rom >>> serial
             )

