{-# LANGUAGE UndecidableInstances #-}

module Take2.Computer.ALU where

import Data.Typeable
import Prelude hiding ((.), id, sum)
import Take2.Computer.Math
import Take2.Computer.Simple
import Take2.Machinery
import Take2.Product (proj)
import Test.QuickCheck.Arbitrary.Generic


data AluCommand a = AluCommand
  { ac_code :: AluOpCode
  , ac_arg1 :: a
  , ac_arg2 :: a
  }
  deriving stock Generic
  deriving anyclass Embed

instance Arbitrary a => Arbitrary (AluCommand a) where
  arbitrary = genericArbitrary
  shrink    = genericShrink


unpackAluCommand
    :: (Embed a, SeparatePorts a, Nameable a, Typeable a)
    => Circuit (AluCommand a) (AluOpCode, (a, a))
unpackAluCommand
    = copy
  >>> proj #ac_code
  *** (copy >>> proj #ac_arg1 *** proj #ac_arg2)


alu
    :: (2 <= SizeOf a, SeparatePorts a, Embed a, Numeric a, Nameable a, SeparatePorts a, Typeable a)
    => Circuit (AluCommand a) (Vec (SizeOf a) Bool)
alu = unpackAluCommand
  >>> ( totalBranch
        $ Cons (AluOpAdd,     snd' >>> addN >>> fst' >>> serial)
        $ Cons (AluOpAnd,     snd' >>> both serial >>> pointwise andGate)
        $ Cons (AluOpOr,      snd' >>> both serial >>> pointwise orGate)
        $ Cons (AluOpXor,     snd' >>> both serial >>> pointwise xorGate)
        $ Cons (AluOpNot,     snd' >>> fst' >>> serial >>> mapV notGate)
        $ Cons (AluOpShiftL,  snd' >>> fst' >>> shiftL >>> serial)
        $ Cons (AluOpShiftR,  snd' >>> fst' >>> shiftR >>> serial)
        $ Cons (AluOpAShiftR, snd' >>> fst' >>> ashiftR >>> serial)
        $ Nil
      )


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
  deriving (Embed, Arbitrary) via (EmbededEnum AluOpCode)


