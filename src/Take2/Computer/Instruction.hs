{-# LANGUAGE UndecidableInstances #-}

module Take2.Computer.Instruction where

import Prelude hiding ((.), id, sum)
import Take2.Machinery
import Data.Proxy
import Take2.Computer.Register


type PC = Word16
type SP = Word16
type W = Word16
type HalfW = Word8
type N = 8


proof :: Proxy (SizeOf Instruction) -> Proxy (SizeOf W)
proof = id

data Instruction
  =      -- src1  -- src2  -- dst
    IAdd Register Register Register
  | IAnd Register Register Register
  | IOr Register Register Register
  | IXOr Register Register Register
  | INot Register Register
  | IMove Register Register
  | ILoadHi Register HalfW
  | ILoadLo Register HalfW
  | IShiftL Register Register
  | IShiftR Register Register
  | IAShiftR Register Register
  | IJump Register HalfW
  | IBranchEq Register Register (Vec 4 Bool)
  | IBranchNeq Register Register (Vec 4 Bool)
  | PADDING_ (Vec 12 Bool)
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass Embed

