{-# LANGUAGE UndecidableInstances #-}

module Take2.Computer.Instruction where

import Prelude hiding ((.), id, sum)
import Take2.Machinery
import Data.Proxy


type PC = Word16
type SP = Word16
type W = Word16
type HalfW = Word8
type N = 8


proof :: Proxy (SizeOf Instruction) -> Proxy (SizeOf W)
proof = id

data Register
  = X
  | Y
  | Z
  | A
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving (Embed, Arbitrary) via EmbededEnum Register

data Instruction
  = IAdd Register Register
  | IAnd Register Register
  | IOr Register Register
  | IXOr Register Register
  | INot Register
  | IMove Register Register
  | ILoadHi Register HalfW
  | ILoadLo Register HalfW
  | IShiftL Register
  | IShiftR Register
  | IAShiftR Register
  | IJumpTo Register
  | IJumpZ Register
  | PADDING_ (Vec 12 Bool)
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass Embed

