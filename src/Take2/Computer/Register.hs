{-# LANGUAGE UndecidableInstances                 #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Take2.Computer.Register where

import Data.Typeable
import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Machinery
import Test.QuickCheck.Arbitrary.Generic (genericArbitrary)


data Register
  = X
  | Y
  | Z
  | A
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
  { reg_PC    :: pc
  , reg_SP    :: sp
  , reg_X     :: word
  , reg_Y     :: word
  , reg_Z     :: word
  , reg_A     :: word
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
    $ #_X :~> proj #reg_X
  :+| #_Y :~> proj #reg_Y
  :+| #_Z :~> proj #reg_Z
  :+| #_A :~> proj #reg_A
  :+| End


setReg
    :: (Embed pc, Embed sp, Embed word, Typeable pc, Typeable sp, Typeable word, SeparatePorts word)
    => Circuit ((Register, word), Registers pc sp word) (Registers pc sp word)
setReg
    = component "setReg"
    $ (reassoc' >>>)
    $ elim
    $ foldElim
    $ #_X :~> replace #reg_X
  :+| #_Y :~> replace #reg_Y
  :+| #_Z :~> replace #reg_Z
  :+| #_A :~> replace #reg_A
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

