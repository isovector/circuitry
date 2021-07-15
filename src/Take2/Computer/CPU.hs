{-# LANGUAGE NoMonomorphismRestriction            #-}
{-# LANGUAGE UndecidableInstances                 #-}

{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Take2.Computer.CPU where

import Prelude hiding ((.), id, sum)
import Take2.Computer.ALU
import Take2.Computer.Bus
import Take2.Computer.Memory
import Take2.Computer.Register
import Take2.Computer.Instruction
import Take2.Machinery



data Step
  = Fetch
  | Decode  W
  | Execute Instruction
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass Embed


cpu
    :: Vec (2 ^ N) W
    -> Circuit () (Registers PC SP W)
cpu rom
    = registers
    $ fixC Fetch
    $ first' snd'
  >>> swap
  >>> first' copy
  >>> second' copy
  >>> reassoc'
  >>> second' reassoc
  >>> second' (first' $ first' $ traceC "step")
  >>> second' ( first'
              $ cpuImpl1
            >>> cpuBus rom
              )
  >>> second' swap
  >>> cpuImpl2
  >>> swap
  >>> first' copy


cpuImpl1
    :: Circuit (Step, Registers PC SP W)
               (BusCommand N W)
cpuImpl1 =
  elim $ foldElim
       $ #_Fetch :~>
          fetch
     :+| #_Decode :->
          snd' >>> incPC
     :+| #_Execute :->
          execute1
     :+| End


todo :: (Embed a, Embed b) => Circuit a b
todo = create >>> snd' >>> serial >>> pad False >>> unsafeParse

aluBinaryOp1
    :: forall name
     . Inj (AluCommand W) (W, W) name
    => InjName name
    -> Circuit ((Register, (Register, Register)), Registers PC SP W)
               (BusCommand N W)
aluBinaryOp1 n
       = first' (second' fst')
     >>> swap
     >>> distribP
     >>> both getReg
     >>> inj @(AluCommand W)   @(W, W)         n
     >>> inj @(BusCommand N W) @(AluCommand W) #_BusAlu

aluUnaryOp1
    :: forall name
     . Inj (AluCommand W) (W) name
    => InjName name
    -> Circuit ((Register, Register), Registers PC SP W)
               (BusCommand N W)
aluUnaryOp1 n
       = first' fst'
     >>> swap
     >>> getReg
     >>> inj @(AluCommand W)   @W              n
     >>> inj @(BusCommand N W) @(AluCommand W) #_BusAlu

aluBinaryOp2
    :: Circuit ( (Register, (Register, Register))
               , (Registers PC SP W, W)
               )
               (Registers PC SP W)
aluBinaryOp2
    = (snd' >>> snd') *** swap
  >>> reassoc
  >>> setReg

aluUnaryOp2
    :: Circuit ( (Register, Register)
               , (Registers PC SP W, W)
               )
               (Registers PC SP W)
aluUnaryOp2
    = snd' *** swap
  >>> reassoc
  >>> setReg

execute1 :: Circuit (Instruction, Registers PC SP W) (BusCommand N W)
execute1
    = elim
    $ foldElim
    $ #_IAdd :-> aluBinaryOp1 #_AluAdd
  :+| #_IAnd :-> aluBinaryOp1 #_AluAnd
  :+| #_IOr  :-> aluBinaryOp1 #_AluOr
  :+| #_IXOr :-> aluBinaryOp1 #_AluXor
  :+| #_INot :-> aluUnaryOp1 #_AluNot
  :+| #_IMove :-> todo
  :+| #_ILoadHi :-> todo
  :+| #_ILoadLo :-> todo -- not actually todo
  :+| #_IShiftL :-> aluUnaryOp1 #_AluShiftL
  :+| #_IShiftR :-> aluUnaryOp1 #_AluShiftR
  :+| #_IAShiftR :-> aluUnaryOp1 #_AluAShiftR
  :+| #_IJumpTo :-> todo
  :+| #_IJumpZ :-> todo
  :+| #_PADDING_ :-> todo
  :+| End

execute2
    :: Circuit (Instruction, (Registers PC SP W, W)) (Registers PC SP W)
execute2
    = elim
    $ foldElim
    $ #_IAdd :-> aluBinaryOp2
  :+| #_IAnd :-> aluBinaryOp2
  :+| #_IOr  :-> aluBinaryOp2
  :+| #_IXOr :-> aluBinaryOp2
  :+| #_INot :-> aluUnaryOp2
  :+| #_IMove :-> second' fst' >>> move
  :+| #_ILoadHi :-> loadHi
  :+| #_ILoadLo :-> loadLo
  :+| #_IShiftL :-> aluUnaryOp2
  :+| #_IShiftR :-> aluUnaryOp2
  :+| #_IAShiftR :-> aluUnaryOp2
  :+| #_IJumpTo :-> todo
  :+| #_IJumpZ :-> todo
  :+| #_PADDING_ :-> todo
  :+| End

move :: Circuit ((Register, Register), Registers PC SP W) (Registers PC SP W)
move
    = swap
  >>> distribP
  >>> getReg
  *** swap
  >>> reassoc
  >>> first' swap
  >>> setReg


loadLo
    :: Circuit ((Register, Word8), (Registers PC SP W, W)) (Registers PC SP W)
loadLo = loadLoOrHigh id


loadHi
    :: Circuit ((Register, Word8), (Registers PC SP W, W)) (Registers PC SP W)
loadHi = loadLoOrHigh swap


loadLoOrHigh
    :: (forall a. Embed a => Circuit (a, a) (a, a))
    -> Circuit ((Register, Word8), (Registers PC SP W, W)) (Registers PC SP W)
loadLoOrHigh f
    = swap *** (fst' >>> copy)
  >>> reassoc
  >>> first'
      ( reassoc'
    >>> second'
        ( first' copy
      >>> reassoc'
      >>> second'
          ( swap
        >>> getReg
        >>> serial
        >>> separate @(SizeOf HalfW)
        >>> f
        >>> snd'
          )
        )
      >>> second' swap
      >>> reassoc
      >>> first' (first' serial >>> f >>> serial >>> unsafeParse @W)
      >>> swap
      )
    >>> setReg



incPC
    :: Circuit (Registers PC SP W) (BusCommand N W)
incPC = proj #reg_PC
    >>> intro @W 1
    >>> inj @(AluCommand W) #_AluAdd
    >>> inj #_BusAlu


cpuBus
    :: Vec (2 ^ N) W
    -> Circuit (BusCommand N W) W
cpuBus rom  = bus rom >>> unsafeParse


cpuImpl2
    :: Circuit (Step, (Registers PC SP W, W)) (Step, Registers PC SP W)
cpuImpl2 =
  elim $ foldElim
       $ #_Fetch
            :~> swap
            >>> first' (inj #_Decode)
     :+| #_Decode
            :-> (decodeInstr >>> inj #_Execute)
            *** (swap >>> replace #reg_PC)
     :+| #_Execute
            :-> execute2
            >>> intro Fetch
            >>> swap
     :+| End


decodeInstr :: Circuit W Instruction
decodeInstr = unsafeReinterpret


fetch
    :: Circuit (Registers PC SP W) (BusCommand N W)
fetch = proj #reg_PC
    >>> serial
    >>> separate @N
    >>> fst'
    >>> unsafeReinterpret @_ @(Addr N)
    >>> inj #_BusROM

