{-# LANGUAGE UndecidableInstances                 #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Take2.Computer.ALU where

import Data.Typeable
import Prelude hiding ((.), id, sum)
import Take2.Computer.Math
import Take2.Computer.Simple
import Take2.Machinery
import Test.QuickCheck.Arbitrary.Generic


data AluCommand a
  = AluAdd a a
  | AluAnd a a
  | AluOr a a
  | AluXor a a
  | AluNot a
  | AluShiftL a
  | AluShiftR a
  | AluAShiftR a
  deriving stock Generic
  deriving anyclass Embed

instance Arbitrary a => Arbitrary (AluCommand a) where
  arbitrary = genericArbitrary
  shrink    = genericShrink


alu
    :: (2 <= SizeOf a, SeparatePorts a, Embed a, Numeric a, Nameable a, SeparatePorts a, Typeable a)
    => Circuit (AluCommand a) (Vec (SizeOf a) Bool)
alu =
  elim_
      $ ( ( #_AluAdd :-> fst' >>> addN >>> fst' >>> serial
         :+| #_AluAnd :-> fst' >>> both serial >>> pointwise andGate
           )
       :+| ( #_AluOr  :-> fst' >>> both serial >>> pointwise orGate
         :+| #_AluXor :-> fst' >>> both serial >>> pointwise xorGate
           )
         )
     :+| ( ( #_AluNot    :-> fst' >>> serial >>> mapV notGate
         :+| #_AluShiftL :-> fst' >>> shiftL >>> serial
           )
       :+| ( #_AluShiftR  :-> fst' >>> shiftR >>> serial
         :+| #_AluAShiftR :-> fst' >>> ashiftR >>> serial
           )
         )

