{-# LANGUAGE UndecidableInstances #-}

module Circuitry.Sing where

import GHC.TypeLits
import Data.Kind (Constraint)

type family Length (xs :: [k]) :: Nat where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

type family MapT (f :: k -> k2) (xs :: [k]) :: [k2] where
  MapT f '[] = '[]
  MapT f (x ': xs) = f x ': MapT f xs

type family Constrain (f :: y -> Constraint) (xs :: [(x, y)]) :: Constraint where
  Constrain f '[] = (() :: Constraint)
  Constrain f ('(n, t) ': xs) = (f n, Constrain f xs)

type family Take (n :: Nat) (xs :: [k]) :: [k] where
  Take 0 xs = '[]
  Take n '[] = '[]
  Take n (x ': xs) = x : Take (n - 1) xs

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
  Drop 0 xs = xs
  Drop n '[] = '[]
  Drop n (x ': xs) = Drop (n - 1) xs

type SplitAt (n :: Nat) (xs :: [k]) = '(Take n xs, Drop n xs)

type FoldBal op xs = Fold_Bal op (Length xs) xs

type family Fold_Bal (op :: k -> k -> k)  (n :: Nat) (xs :: [k]) :: k where
  Fold_Bal op n '[] = TypeError ('Text "Empty Fold_Bal")
  Fold_Bal op n '[a] = a
  Fold_Bal op n xs = Fold_Bal2 op n xs (Div n 2) (SplitAt (Div n 2) xs)

type family Fold_Bal2 op n xs nl lr  where
  Fold_Bal2 op n xs nl '(l, r) = Fold_Bal op nl l `op` Fold_Bal op (n - nl) r

-- foldBal :: (a -> a -> a) -> a -> [a] -> a
-- foldBal op0 x0 xs0 = fold_bal op0 x0 (length xs0) xs0
--   where
--     fold_bal :: (a -> a -> a) -> a -> Int -> [a] -> a
--     fold_bal _ x _ [] = x
--     fold_bal _ _ _ [a] = a
--     fold_bal op x n xs =
--       let !nl = n `div` 2
--           (l,r) = splitAt nl xs
--        in fold_bal op x nl l
--                 `op` fold_bal op x (n - nl) r

