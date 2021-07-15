{-# LANGUAGE UndecidableInstances                 #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Take2.Computer.Register where

import Data.Typeable
import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Machinery
import Test.QuickCheck.Arbitrary.Generic (genericArbitrary)


data Register
  = R1
  | R2
  | R3
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | R16
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving (Embed, Arbitrary) via EmbededEnum Register

data Flags = Flags
  { f_neg      :: Bool
  , f_overflow :: Bool
  , f_zero     :: Bool
  , f_carry    :: Bool
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass Embed

data Registers pc sp word = Registers
  { reg_PC :: pc
  , reg_SP :: sp
  , reg_R1  :: word
  , reg_R2  :: word
  , reg_R3  :: word
  , reg_R4  :: word
  , reg_R5  :: word
  , reg_R6  :: word
  , reg_R7  :: word
  , reg_R8  :: word
  , reg_R9  :: word
  , reg_R10 :: word
  , reg_R11 :: word
  , reg_R12 :: word
  , reg_R13 :: word
  , reg_R14 :: word
  , reg_R15 :: word
  , reg_R16 :: word
  , reg_flags :: Flags
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass Embed

instance Arbitrary Flags where
  arbitrary = genericArbitrary

instance (Arbitrary pc, Arbitrary sp, Arbitrary word) => Arbitrary (Registers pc sp word) where
  arbitrary = genericArbitrary



getReg
    :: (Embed pc, Embed sp, Embed word, Typeable pc, Typeable sp, Typeable word, SeparatePorts word)
    => Circuit (Registers pc sp word, Register) word
getReg
    = component "getReg"
    $ (swap >>>)
    $ elim
    $ foldElim
    $ #_R1  :~> proj #reg_R1
  :+| #_R2  :~> proj #reg_R2
  :+| #_R3  :~> proj #reg_R3
  :+| #_R4  :~> proj #reg_R4
  :+| #_R5  :~> proj #reg_R5
  :+| #_R6  :~> proj #reg_R6
  :+| #_R7  :~> proj #reg_R7
  :+| #_R8  :~> proj #reg_R8
  :+| #_R9  :~> proj #reg_R9
  :+| #_R10 :~> proj #reg_R10
  :+| #_R11 :~> proj #reg_R11
  :+| #_R12 :~> proj #reg_R12
  :+| #_R13 :~> proj #reg_R13
  :+| #_R14 :~> proj #reg_R14
  :+| #_R15 :~> proj #reg_R15
  :+| #_R16 :~> proj #reg_R16
  :+| End


setReg
    :: (Embed pc, Embed sp, Embed word, Typeable pc, Typeable sp, Typeable word, SeparatePorts word)
    => Circuit ((Register, word), Registers pc sp word) (Registers pc sp word)
setReg
    = component "setReg"
    $ (reassoc' >>>)
    $ elim
    $ foldElim
    $ #_R1  :~> replace #reg_R1
  :+| #_R2  :~> replace #reg_R2
  :+| #_R3  :~> replace #reg_R3
  :+| #_R4  :~> replace #reg_R4
  :+| #_R5  :~> replace #reg_R5
  :+| #_R6  :~> replace #reg_R6
  :+| #_R7  :~> replace #reg_R7
  :+| #_R8  :~> replace #reg_R8
  :+| #_R9  :~> replace #reg_R9
  :+| #_R10 :~> replace #reg_R10
  :+| #_R11 :~> replace #reg_R11
  :+| #_R12 :~> replace #reg_R12
  :+| #_R13 :~> replace #reg_R13
  :+| #_R14 :~> replace #reg_R14
  :+| #_R15 :~> replace #reg_R15
  :+| #_R16 :~> replace #reg_R16
  :+| End


registers
    :: forall pc sp word a b
     . ( Embed pc
       , Embed sp
       , Embed word
       , Embed a
       , Embed b
       )
    => Circuit (a, Registers pc sp word) (b, Registers pc sp word)
    -> Circuit a b
registers = fixC $ reify $ V.repeat False

