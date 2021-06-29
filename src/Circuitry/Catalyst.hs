{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wall                               #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-do-bind                 #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Circuitry.Catalyst
  ( module Circuitry.Category
  , module Circuitry.Catalyst
  ) where

import           Circuitry.Category
import           Data.Bool (bool)
import           Data.Function (fix)
import           Data.MemoTrie
import           Data.Profunctor.Choice (unleft)
import           Data.Profunctor.Types
import           Data.Word (Word8)
import           Numeric.Natural (Natural)
import           Prelude hiding (id, (.), sum, zip)
import           Test.QuickCheck (CoArbitrary, Testable (property), Arbitrary (arbitrary), counterexample, applyFun, Function (function), functionMap, forAllShrink, shrink, (===))
import           Test.QuickCheck.Arbitrary (CoArbitrary(coarbitrary))
import           Test.QuickCheck.Checkers



instance Arbitrary Natural where
  arbitrary = fmap (fromIntegral . abs @Integer) arbitrary

instance CoArbitrary Natural where
  coarbitrary = coarbitrary @Integer . fromIntegral

instance Function Natural where
  function = functionMap fromIntegral (fromIntegral @Integer . abs)

instance (Show a, EqProp b, CoArbitrary r, Arbitrary a, Arbitrary r, Show r, Show b, Function r) => EqProp (Roar r a b) where
  Roar r1 =-= Roar r2 = property $ do
    t <- arbitrary
    pure $ forAllShrink arbitrary shrink $ \f' -> do
    let f = applyFun f'
        v1 = r1 f t
        v2 = r2 f t
    counterexample (show t) $ counterexample (show v1) $ counterexample (show v2) $ v1 =-= v2


instance EqProp Word8 where
  (=-=) = (===)


newtype Roar r a b = Roar { runRoar :: (r -> a) -> (r -> b) }
  deriving stock Functor

instance Distrib (Roar r) where
  distrib = Roar $ \ f r -> case f r of { (a, e) -> case e of
                                            (Left b) -> Left (a, b)
                                            (Right c) -> Right (a, c) }
  factor = Roar (\ f r -> case f r of
    Left x0 -> case x0 of { (a, b) -> (a, Left b) }
    Right x0 -> case x0 of { (a, c) -> (a, Right c) } )


instance Profunctor (Roar r) where
  lmap fab (Roar f) = Roar (\ fra -> f (fab . fra))
  rmap fbc (Roar f) = Roar (\ fra -> fbc . f fra)

instance Category (Roar r) where
  type Ok (Roar r) = TrivialConstraint
  id = Roar id
  (.) (Roar f) (Roar g) = Roar (f . g)

instance SymmetricProduct (Roar r) where
  swap = Roar (\ f r -> swap $ f r)
  reassoc = Roar (\ f r -> reassoc $ f r)

instance MonoidalProduct (Roar r) where
  first' (Roar f) = Roar $ \rac r ->
     (f (fst . rac) r, snd $ rac r)

instance Cartesian (Roar r) where
  consume = Roar (\ _ _ -> ())
  copy = Roar (\ fra r -> (fra r, fra r))
  fst' = Roar (\ f r -> fst $ f r)
  snd' = Roar (\ f r -> snd $ f r)

instance Fixed (Roar r) where
  fixL (Roar f) = Roar $ \ fra r ->
     fst $ fix $ \(_, s) -> f ((, s) . fra) r
  fixR f = fixL $ swap >>> f >>> swap

instance SymmetricSum (Roar r) where
  swapE = Roar (\ f r -> swapE $ f r)
  reassocE = Roar (\ f r -> reassocE $ f r)

instance MonoidalSum (Roar r) where
  left (Roar f) = Roar $ \ rac r ->
    either (Left . flip f r . const) Right $ rac r

instance Cocartesian (Roar r) where
  injectL = Roar (\ fra r -> Left (fra r))
  injectR = Roar (\ fra r -> Right (fra r))
  unify = Roar (\ f r -> either id id $ f r)
  tag = Roar $ \ f r ->
    let (b, a) = f r
     in case b of
          False -> Left a
          True  -> Right a

instance Recursive (Roar r) where
  recurseL (Roar f) = Roar $ \fra -> unleft $ either (\r -> f (Left . fra) r) Right
  recurseR x = recurseL $ swapE >>> x >>> swapE


arr :: (a -> b) -> Roar r a b
arr fab = Roar (\ fra r -> fab (fra r))



loop
    :: s
    -> ((Time -> (x, s)) -> Time -> (y, s))
    -> (Time -> x)
    -> Time
    -> (y, s)
loop b f tx = memo $ \case
  0 -> f ((, b) . tx) 0
  t -> let (_, s) = loop b f tx $ t - 1
        in f ((, s) . tx) t


spike :: Time -> Time -> Bool
spike n t = bool False True $ n == t

type Time = Int

