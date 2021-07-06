{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Take2.Computer.Bus where

import Prelude hiding ((.), id, sum)
import Take2.Computer.Simple
import Take2.Computer.Addressed
import Take2.Machinery
import Take2.Computer.Memory
import Take2.Computer.ALU
import Data.Typeable (Typeable)


mkBus
    :: (Embed dev, Embed a, Embed b)
    => Vec (2 ^ SizeOf dev) (Circuit (Bool, a) b)
    -> Circuit (dev, a) b
mkBus devs = (unsafeReinterpret >>> decode) *** cloneV
          >>> zipVC
          >>> parallelMetaV devs
          >>> mapV serial
          >>> transposeV
          >>> mapV unsafeShort
          >>> unsafeParse

data BusId = MemoryBus | AluBus
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving (Arbitrary, Embed) via (EmbededEnum BusId)


unsafeFromLeft :: forall a b. (Embed a, Embed b) => Circuit (Either a b) a
unsafeFromLeft = serial
             >>> unconsC
             >>> snd'
             >>> separate @(SizeOf a)
             >>> fst'
             >>> unsafeParse


bus :: forall n word
     . ( Embed word
       , KnownNat n
       , Nameable word
       , SeparatePorts word
       , Typeable word
       , Numeric word
       , 2 <= SizeOf word
       )
    => Circuit (BusId, Either (MemoryCommand Identity n word) (AluCommand word))
               (Vec (SizeOf word) Bool)
bus =
  mkBus @BusId $ ( second' unsafeFromLeft
               >>> unsafeReinterpret
               >>> (memoryCell @n @word)
                 )
              :> ( aluBusComponent @n @word
                 )
              :> Nil


aluBusComponent
    :: forall n word.
       ( Embed word
       , KnownNat n
       , Nameable word
       , SeparatePorts word
       , Typeable word
       , Numeric word
       , 2 <= SizeOf word
       ) => Circuit (Bool, Either (MemoryCommand Identity n word) (AluCommand word)) (Vec (SizeOf word) Bool)
aluBusComponent = second' (swapE >>> unsafeFromLeft)
               >>> swap
               >>> first' serial
               >>> tribufAll
               >>> unsafeParse
               >>> (alu @word)

------------------------------------------------------------------------------
-- | Always provids a Z b. Useful for filling out the cases in mkBus.
noBusDevice :: (Embed a, Embed b) => Circuit (Bool, a) b
noBusDevice = consume
          >>> intro False
          >>> first' (serial >>> pad False)
          >>> tribufAll
          >>> unsafeParse

