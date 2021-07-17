{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module TruthTable (Enumerable (..), EnumerateEnum(..), truthTable) where

import Control.Applicative (liftA2)
import Data.Coerce (coerce)
import Data.List (intercalate)
import Data.Maybe (isJust, isNothing, fromJust)
import GHC.Generics
import GHC.TypeLits (type (<=))
import Circuitry.Circuit
import Circuitry.Embed


class Enumerable a where
  enumerate :: [a]
  default enumerate :: (Generic a, GEnumerable (Rep a)) => [a]
  enumerate = fmap to genumerate


class GEnumerable f where
  genumerate :: [f x]

instance GEnumerable f => GEnumerable (M1 _1 _2 f) where
  genumerate = fmap M1 genumerate

instance (GEnumerable f, GEnumerable g) => GEnumerable (f :*: g) where
  genumerate = liftA2 (:*:) genumerate genumerate

instance (GEnumerable f, GEnumerable g) => GEnumerable (f :+: g) where
  genumerate = fmap L1 genumerate <> fmap R1 genumerate

instance GEnumerable U1 where
  genumerate = pure U1

instance Enumerable a => GEnumerable (K1 _1 a) where
  genumerate = fmap K1 enumerate


newtype EnumerateEnum a = EnumerateEnum a

instance (Enum a, Bounded a) => Enumerable (EnumerateEnum a) where
  enumerate = coerce $ enumFromTo @a minBound maxBound


deriving anyclass instance Enumerable Bool
deriving anyclass instance (Enumerable a, Enumerable b) => Enumerable (a, b)
deriving anyclass instance (Enumerable a, Enumerable b) => Enumerable (Either a b)
deriving anyclass instance (Enumerable a) => Enumerable (Maybe a)


class SplitProduct a where
  splitProduct :: a -> [String]

instance {-# OVERLAPPING #-} (SplitProduct a, SplitProduct b) => SplitProduct (a, b) where
  splitProduct (a, b) = splitProduct a <> splitProduct b

instance Show a => SplitProduct a where
  splitProduct = pure . show


truthTable
    :: forall a b
     . ( Show a
       , Show b
       , Enumerable a
       , Embed a
       , Embed b
       , SplitProduct a
       , SplitProduct b
       , 1 <= SizeOf b
       )
    => Circuit a b
    -> String
truthTable c = buildTable $ do
  a <- enumerate @a
  pure $ (splitProduct a, ) $
    let v = evalCircuitMV c (fmap Just $ embed a) 0
     in case (all isJust v, all isNothing v) of
          (True, _) -> splitProduct $ reify @b $ fmap fromJust v
          (_, True) -> pure "high Z"
          (_, _) -> error "circuit for truthTable isn't total"


buildTable :: [([String], [String])] -> String
buildTable ls@((i,o):_)
  = unlines
  $ buildHeader (length i) (length o)
  : buildSpacer (length i + length o)
  : fmap (uncurry buildRow) ls
buildTable [] = error "empty table"


buildHeader :: Int -> Int -> String
buildHeader ins outs
  = columnize
  $ fmap (mappend "In " . show) [1 .. ins] <> fmap (mappend "Out " . show) [1 .. outs]


buildSpacer :: Int -> String
buildSpacer cols
  = columnize
  $ "---" <$ [1 .. cols]


buildRow :: [String] -> [String] -> String
buildRow ins outs = columnize $ ins <> outs


columnize :: [String] -> String
columnize ins = "| " <> intercalate " | " ins <> " |"

