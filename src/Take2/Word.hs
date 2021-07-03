module Take2.Word (Word2 (..), Word3(..), Word4 (..)) where

import Data.Bits
import Data.Typeable
import Data.Ratio
import Test.QuickCheck (Arbitrary, arbitrary)
import Test.QuickCheck.Function

newtype Word2 = Word2 { unWord2 :: Int } deriving (Eq, Ord)

instance Arbitrary Word2 where
  arbitrary = word2 <$> arbitrary

instance Function Word2 where
  function = functionIntegral


word2 :: Int -> Word2;  word2 = Word2 . narrowU 2
oWord2 ::(Int->Int->Int)->(Word2->Word2->Word2); oWord2 = oNewtype word2 unWord2

fWord2 :: (Int->Int) -> (Word2->Word2) ; fWord2 = fNewtype word2 unWord2

instance Show Word2 where show = show . unWord2
instance Read Word2 where readsPrec = readsPrecNewtype word2
instance Num Word2 where (+) = oWord2 (+);  abs    = fWord2 abs
                         (-) = oWord2 (-);  signum = fWord2 signum
                         (*) = oWord2 (*);  fromInteger = word2 . fromInteger
instance Real Word2 where toRational (Word2 x) = fromIntegral x % 1
instance Integral Word2 where quotRem = otNewtype word2 unWord2 quotRem
                              toInteger = toInteger . unWord2
instance Bounded Word2 where maxBound = Word2 3; minBound = Word2 0
instance Enum Word2 where toEnum   = word2;   enumFrom     = boundedEnumFrom
                          fromEnum = unWord2; enumFromThen = boundedEnumFromThen
deriving instance Typeable Word2

instance Bits Word2 where
  (.&.) = oWord2 (.&.)
  (.|.) = oWord2 (.|.)
  xor = oWord2 xor
  complement = fWord2 complement
  shift x n = fWord2 (flip shift n) x
  rotate x n = fWord2 (flip rotate n) x
  bitSize _ = 2
  bitSizeMaybe _ = Just 2
  isSigned _ = False
  testBit = testBit . unWord2
  bit = word2 . bit
  popCount = popCount . unWord2

newtype Word3 = Word3 { unWord3 :: Int } deriving (Eq, Ord)

instance Arbitrary Word3 where
  arbitrary = word3 <$> arbitrary

instance Function Word3 where
  function = functionIntegral


word3 :: Int -> Word3;  word3 = Word3 . narrowU 3
oWord3 ::(Int->Int->Int)->(Word3->Word3->Word3); oWord3 = oNewtype word3 unWord3

fWord3 :: (Int->Int) -> (Word3->Word3) ; fWord3 = fNewtype word3 unWord3

instance Show Word3 where show = show . unWord3
instance Read Word3 where readsPrec = readsPrecNewtype word3
instance Num Word3 where (+) = oWord3 (+);  abs    = fWord3 abs
                         (-) = oWord3 (-);  signum = fWord3 signum
                         (*) = oWord3 (*);  fromInteger = word3 . fromInteger
instance Real Word3 where toRational (Word3 x) = fromIntegral x % 1
instance Integral Word3 where quotRem = otNewtype word3 unWord3 quotRem
                              toInteger = toInteger . unWord3
instance Bounded Word3 where maxBound = Word3 7; minBound = Word3 0
instance Enum Word3 where toEnum   = word3;   enumFrom     = boundedEnumFrom
                          fromEnum = unWord3; enumFromThen = boundedEnumFromThen
deriving instance Typeable Word3

instance Bits Word3 where
  (.&.) = oWord3 (.&.)
  (.|.) = oWord3 (.|.)
  xor = oWord3 xor
  complement = fWord3 complement
  shift x n = fWord3 (flip shift n) x
  rotate x n = fWord3 (flip rotate n) x
  bitSize _ = 3
  bitSizeMaybe _ = Just 3
  isSigned _ = False
  testBit = testBit . unWord3
  bit = word3 . bit
  popCount = popCount . unWord3

newtype Word4 = Word4 { unWord4 :: Int } deriving (Eq, Ord)

instance Arbitrary Word4 where
  arbitrary = word4 <$> arbitrary

instance Function Word4 where
  function = functionIntegral


word4 :: Int -> Word4;  word4 = Word4 . narrowU 4
oWord4 ::(Int->Int->Int)->(Word4->Word4->Word4); oWord4 = oNewtype word4 unWord4

fWord4 :: (Int->Int) -> (Word4->Word4) ; fWord4 = fNewtype word4 unWord4

instance Show Word4 where show = show . unWord4
instance Read Word4 where readsPrec = readsPrecNewtype word4
instance Num Word4 where (+) = oWord4 (+);  abs    = fWord4 abs
                         (-) = oWord4 (-);  signum = fWord4 signum
                         (*) = oWord4 (*);  fromInteger = word4 . fromInteger
instance Real Word4 where toRational (Word4 x) = fromIntegral x % 1
instance Integral Word4 where quotRem = otNewtype word4 unWord4 quotRem
                              toInteger = toInteger . unWord4
instance Bounded Word4 where maxBound = Word4 15; minBound = Word4 0
instance Enum Word4 where toEnum   = word4;   enumFrom     = boundedEnumFrom
                          fromEnum = unWord4; enumFromThen = boundedEnumFromThen
deriving instance Typeable Word4

instance Bits Word4 where
  (.&.) = oWord4 (.&.)
  (.|.) = oWord4 (.|.)
  xor = oWord4 xor
  complement = fWord4 complement
  shift x n = fWord4 (flip shift n) x
  rotate x n = fWord4 (flip rotate n) x
  bitSize _ = 4
  bitSizeMaybe _ = Just 4
  isSigned _ = False
  testBit = testBit . unWord4
  bit = word4 . bit
  popCount = popCount . unWord4


boundedEnumFrom :: (Ord a,Bounded a,Enum a) => a -> [a]
boundedEnumFrom x = [x..maxBound]

boundedEnumFromThen :: (Ord a,Bounded a,Enum a) => a -> a -> [a]
boundedEnumFromThen x y | x > y     = [x,y..minBound]
                        | otherwise = [x,y..maxBound]

oNewtype :: (a -> b) -> (b -> a) -> (a -> a -> a) -> (b -> b -> b)
oNewtype con des o = \x y -> con $ des x `o` des y


otNewtype :: (a -> b) -> (b -> a) -> (a -> a -> (a,a)) -> (b -> b -> (b,b))
otNewtype con des o = \x y -> mapTuple con $ des x `o` des y


mapTuple :: (a -> b) -> (a,a) -> (b,b)
mapTuple f (x,y) = (f x, f y)


readsPrecNewtype :: Read a => (a -> b) -> Int -> String -> [(b,String)]
readsPrecNewtype con n = map (mapFst con) . readsPrec n


mapFst :: (a -> b) -> (a,c) -> (b,c)
mapFst f (x,y) = (f x,y)


fNewtype :: (a -> b) -> (b -> a) -> (a -> a) -> (b -> b)
fNewtype con des f = con . f . des


narrowU :: Int -> Int -> Int
narrowU w i = i `mod` 2^w

