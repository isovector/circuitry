module Take2.Word (Word4 (..)) where

import Data.Bits
import Data.Typeable
import Data.Ratio
import Test.QuickCheck (Arbitrary, arbitrary)
import Test.QuickCheck.Function

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
-- | Deprecated.  Use 'Word4'.
type UInt4 = Word4
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

