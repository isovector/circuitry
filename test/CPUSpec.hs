module CPUSpec where

import qualified Clash.Sized.Vector as V
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.CPU
import           Take2.Computer.Instruction
import           Take2.Computer.Register
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck


prog :: [Instruction]
prog =
  [ ILoadLo R1 1
  , ILoadLo R2 2
  , ILoadLo R3 3
  , ILoadLo R4 4
  , ILoadHi R5 1
  , ILoadLo R5 5
  , IAdd R16 R1 R16
  , IAdd R16 R2 R16
  , IAdd R16 R3 R16
  , IAdd R16 R4 R16
  , IAdd R16 R5 R16
  ]


runProg :: Circuit () (Registers PC SP W)
runProg
    = cpu
    . fmap (reify . embed)
    . V.unsafeFromList
    . mappend prog
    . repeat
    . PADDING_
    $ V.repeat False


testReg :: Registers PC SP W
testReg
  = Registers
      { reg_PC = 0
      , reg_SP = 0
      , reg_R1 = 1
      , reg_R2 = 2
      , reg_R3 = 3
      , reg_R4 = 4
      , reg_R5 = 5
      , reg_R6 = 6
      , reg_R7 = 7
      , reg_R8 = 8
      , reg_R9 = 9
      , reg_R10 = 10
      , reg_R11 = 11
      , reg_R12 = 12
      , reg_R13 = 13
      , reg_R14 = 14
      , reg_R15 = 15
      , reg_R16 = 16
      , reg_flags = Flags False False False False
      }




-- spec :: Spec
-- spec = do
--   let empty = InjName :-> (consume >>> serial >>> pad False >>> unsafeParse)

--   prop "eliminates ctor1" $ \(val1 :: Bool) (val2 :: Word4) -> do
--     evalCircuit
--         (elim_ $ foldElim
--                $ #_Ctor1 :=> id
--              :+| empty
--              :+| empty
--              :+| empty
--              :+| End

--         )
--         (Ctor1 val1 val2)
--         0
--       === Just (val1, val2)

--   prop "eliminates ctor2" $ \(val :: Word4) -> do
--     evalCircuit
--         (elim_ $ foldElim
--                $ empty
--                :+| #_Ctor2 :=> id
--                :+| empty
--                :+| empty
--                :+| End
--         )
--         (Ctor2 val)
--         0
--       === Just val

--   prop "eliminates ctor3" $ \(val :: Word8) -> do
--     evalCircuit
--         (elim_ $ foldElim
--                $ empty
--              :+| empty
--              :+| #_Ctor3 :=> id
--              :+| empty
--              :+| End
--         )
--         (Ctor3 val)
--         0
--       === Just val

--   prop "eliminates ctor4" $ \(val :: Maybe Bool) -> do
--     evalCircuit
--         (elim_ $ foldElim
--                $ empty
--              :+| empty
--              :+| empty
--              :+| #_Ctor4 :=> id
--              :+| End
--         )
--         (Ctor4 val)
--         0
--       === Just val

--   prop "injects ctor1" $ \(val1 :: Bool) (val2 :: Word4) -> do
--     evalCircuit
--         (inj #_Ctor1)
--         (val1, val2)
--         0
--       === Just (Ctor1 val1 val2)

--   prop "injects ctor2" $ \(val :: Word4) -> do
--     evalCircuit
--         (inj #_Ctor2)
--         val
--         0
--       === Just (Ctor2 val)

--   prop "injects ctor3" $ \(val :: Word8) -> do
--     evalCircuit
--         (inj #_Ctor3)
--         val
--         0
--       === Just (Ctor3 val)

--   prop "injects ctor4" $ \(val :: Maybe Bool) -> do
--     evalCircuit
--         (inj #_Ctor4)
--         val
--         0
--       === Just (Ctor4 val)





