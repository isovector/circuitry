{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module CoproductSpec where

import Prelude hiding ((.), id, sum)
import Take2.Machinery
import Test.Hspec
import Test.Hspec.QuickCheck


data Coprod
  = Ctor1 Bool Word4
  | Ctor2 Word4
  | Ctor3 Word8
  | Ctor4 (Maybe Bool)
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Embed)

instance Arbitrary Coprod where
  arbitrary = oneof
    [ Ctor1 <$> arbitrary <*> arbitrary
    , Ctor2 <$> arbitrary
    , Ctor3 <$> arbitrary
    , Ctor4 <$> arbitrary
    ]


spec :: Spec
spec = do
  let empty = InjName :-> (consume >>> serial >>> pad False >>> unsafeParse)

  prop "eliminates ctor1" $ \(val1 :: Bool) (val2 :: Word4) -> do
    evalCircuit
        (elim $ ( #_Ctor1 :-> id
              :+| empty
                )
            :+| ( empty
              :+| empty
                )
        )
        (Ctor1 val1 val2)
        0
      === Just (val1, val2)

  prop "eliminates ctor2" $ \(val :: Word4) -> do
    evalCircuit
        (elim $ ( empty
              :+| #_Ctor2 :-> id
                )
            :+| ( empty
              :+| empty
                )
        )
        (Ctor2 val)
        0
      === Just val

  prop "eliminates ctor3" $ \(val :: Word8) -> do
    evalCircuit
        (elim $ ( empty
              :+| empty
                )
            :+| ( #_Ctor3 :-> id
              :+| empty
                )
        )
        (Ctor3 val)
        0
      === Just val

  prop "eliminates ctor4" $ \(val :: Maybe Bool) -> do
    evalCircuit
        (elim $ ( empty
              :+| empty
                )
            :+| ( empty
              :+| #_Ctor4 :-> id
                )
        )
        (Ctor4 val)
        0
      === Just val

  prop "injects ctor1" $ \(val1 :: Bool) (val2 :: Word4) -> do
    evalCircuit
        (inj #_Ctor1)
        (val1, val2)
        0
      === Just (Ctor1 val1 val2)

  prop "injects ctor2" $ \(val :: Word4) -> do
    evalCircuit
        (inj #_Ctor2)
        val
        0
      === Just (Ctor2 val)

  prop "injects ctor3" $ \(val :: Word8) -> do
    evalCircuit
        (inj #_Ctor3)
        val
        0
      === Just (Ctor3 val)

  prop "injects ctor4" $ \(val :: Maybe Bool) -> do
    evalCircuit
        (inj #_Ctor4)
        val
        0
      === Just (Ctor4 val)




