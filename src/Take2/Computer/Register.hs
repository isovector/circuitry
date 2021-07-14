{-# LANGUAGE UndecidableInstances      #-}

module Take2.Computer.Register where

import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Machinery


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

