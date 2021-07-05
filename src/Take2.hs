{-# LANGUAGE AllowAmbiguousTypes #-}

module Take2 where

import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Simple
import           Take2.Computer.Math
import           Take2.Machinery



data RW = R | W
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed


alu
    :: (2 <= SizeOf a, SeparatePorts a, Embed a, Numeric a)
    => Circuit (AluOpCode, (a, a)) (Vec (SizeOf a) Bool)
alu =
  branch
    $ Cons (AluOpAdd,     addN >>> fst' >>> serial)
    $ Cons (AluOpAnd,     both serial >>> pointwise andGate)
    $ Cons (AluOpOr,      both serial >>> pointwise orGate)
    $ Cons (AluOpXor,     both serial >>> pointwise xorGate)
    $ Cons (AluOpNot,     fst' >>> serial >>> mapV notGate)
    $ Cons (AluOpShiftL,  fst' >>> shiftL >>> serial)
    $ Cons (AluOpShiftR,  fst' >>> shiftR >>> serial)
    $ Cons (AluOpAShiftR, fst' >>> ashiftR >>> serial)
    $ Nil


data AluOpCode
  = AluOpAdd
  | AluOpAnd
  | AluOpOr
  | AluOpXor
  | AluOpNot
  | AluOpShiftL
  | AluOpShiftR
  | AluOpAShiftR
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass Embed

instance Arbitrary AluOpCode where
  arbitrary
    = let
        terminal
          = [pure AluOpAdd, pure AluOpAnd, pure AluOpOr, pure AluOpXor,
             pure AluOpNot, pure AluOpShiftL, pure AluOpShiftR,
             pure AluOpAShiftR]
       in oneof terminal

