{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module CoproductSpec where

import Prelude hiding ((.), id, sum)
import Circuitry.Machinery
import Test.Hspec
import Test.Hspec.QuickCheck
import Data.Typeable (Typeable)
import GHC.TypeLits (KnownSymbol)
import qualified Clash.Sized.Vector as V


data Coprod
  = Ctor1 Bool Word4
  | Ctor2 Word4
  | Ctor3 Word8
  | Ctor4 (Maybe Bool)
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Embed, Reify)

empty :: (Typeable x, KnownSymbol name, Embed x, Embed b, Embed r) => Elim ('Leaf '(name, x)) b r
empty = InjName :-> (consume >>> serial >>> pad False >>> unsafeParse)

test :: Circuit Coprod (Word4)
test =
  elim_ $ foldElim
        $ #_Ctor1 :=> snd'
      :+| #_Ctor2 :=> id
      :+| #_Ctor3 :=> serial >>> separate >>> fst' >>> unsafeParse
      :+| #_Ctor4 :=> serial >>> pad False >>> unsafeParse
      :+| End


instance Arbitrary Coprod where
  arbitrary = oneof
    [ Ctor1 <$> arbitrary <*> arbitrary
    , Ctor2 <$> arbitrary
    , Ctor3 <$> arbitrary
    , Ctor4 <$> arbitrary
    ]


spec :: Spec
spec = do
  prop "eliminates ctor1" $ \(val1 :: Bool) (val2 :: Word4) -> do
    evalCircuit test
        (Ctor1 val1 val2)
        0
      === Just val2

  prop "eliminates ctor2" $ \(val :: Word4) -> do
    evalCircuit
        test
        (Ctor2 val)
        0
      === Just val

  prop "eliminates ctor3" $ \(val1 :: Word4) (val2 :: Word4) -> do
    evalCircuit
        test
        (Ctor3 $ reify $ embed val1 V.++ embed val2)
        0
      === Just val1

  prop "eliminates ctor4" $ \(val :: Maybe Bool) -> do
    evalCircuit
        (elim_ $ foldElim
               $ empty
             :+| empty
             :+| empty
             :+| #_Ctor4 :=> id
             :+| End
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




