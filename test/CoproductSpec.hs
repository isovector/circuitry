module CoproductSpec where

import Prelude hiding ((.), id, sum)
import Take2.Machinery
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck


data Coprod
  = Ctor1 Bool
  | Ctor2 Word4
  | Ctor3 Word8
  | Ctor4 (Maybe Bool)
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Embed)

instance Arbitrary Coprod where
  arbitrary = oneof
    [ Ctor1 <$> arbitrary
    , Ctor2 <$> arbitrary
    , Ctor3 <$> arbitrary
    , Ctor4 <$> arbitrary
    ]


test :: Circuit Coprod Bool
test = (elim $ ( Elim id
              :+| Elim (consume >>> serial >>> pad False >>> unsafeParse)
                )
            :+| ( Elim (consume >>> serial >>> pad False >>> unsafeParse)
              :+| Elim (consume >>> serial >>> pad False >>> unsafeParse)
                )
        )


spec :: Spec
spec = do
  let empty = Elim (consume >>> serial >>> pad False >>> unsafeParse)

  prop "eliminates ctor1" $ \(val :: Bool) -> do
    evalCircuit
        (elim $ ( Elim id
              :+| empty
                )
            :+| ( empty
              :+| empty
                )
        )
        (Ctor1 val)
        0
      === Just val

  prop "eliminates ctor2" $ \(val :: Word4) -> do
    evalCircuit
        (elim $ ( empty
              :+| Elim id
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
            :+| ( Elim id
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
              :+| Elim id
                )
        )
        (Ctor4 val)
        0
      === Just val




