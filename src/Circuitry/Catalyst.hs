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
import           Data.Profunctor.Choice (unleft)
import           Data.Profunctor.Types
import           Data.Word (Word8)
import           Numeric.Natural (Natural)
import           Prelude hiding (id, (.), sum, zip)
import           Test.QuickCheck (CoArbitrary, Testable (property), Arbitrary (arbitrary), counterexample, applyFun, Function (function), functionMap, forAllShrink, shrink, (===))
import           Test.QuickCheck.Arbitrary (CoArbitrary(coarbitrary))
import           Test.QuickCheck.Checkers
import Control.Applicative (liftA2)
import Data.Bifunctor (bimap)



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

newtype Signal a b = Signal
  { pumpSignal :: a -> (Signal a b, b)
  }
  deriving stock Functor

instance Applicative (Signal a) where
  pure b = Signal $ const $ (pure b, b)
  (<*>) (Signal sf) (Signal sb) = Signal $ \a ->
    let (sf', f) = sf a
        (sa', b) = sb a
     in (sf' <*> sa', f b)


instance (CoArbitrary a, Arbitrary b) => Arbitrary (Signal a b) where
  arbitrary = Signal <$> arbitrary

instance Profunctor Signal where
  dimap f g (Signal h) = Signal $ (dimap f g *** g) . h . f

instance Category Signal where
  type Ok Signal = TrivialConstraint
  id = Signal $ \a -> (id, a)
  Signal g . Signal f = Signal $ \a ->
    let (sf, b) = f a
        (sg, c) = g b
     in (sg . sf, c)
  {-# INLINE id #-}
  {-# INLINE (.) #-}


primSignal :: (a -> b) -> Signal a b
primSignal f = fix $ \me -> Signal $ \a -> (me, f a)
{-# INLINE primSignal #-}


instance Distrib Signal where
  distrib = primSignal distrib
  factor = primSignal factor

instance SymmetricProduct Signal where
  swap = primSignal swap
  reassoc = primSignal reassoc
  reassoc' = primSignal reassoc'

instance MonoidalProduct Signal where
  (***) (Signal f) (Signal g) = Signal $ \(al, ar) ->
    let (sf, bl) = f al
        (sg, br) = g ar
     in (sf *** sg, (bl, br))
  {-# INLINE (***) #-}

instance SymmetricSum Signal where
  swapE = primSignal swapE
  reassocE = primSignal reassocE

instance MonoidalSum Signal where
  (+++) sf sg = Signal $ \case
     Left  al -> (+++ sg) *** Left  $ pumpSignal sf al
     Right ar -> (sf +++) *** Right $ pumpSignal sg ar
  {-# INLINE (+++) #-}

instance Cartesian Signal where
  consume = primSignal consume
  copy = primSignal copy
  fst' = primSignal fst'
  snd' = primSignal snd'

instance Cocartesian Signal where
  injectL = primSignal injectL
  injectR = primSignal injectR
  unify = primSignal unify
  tag = primSignal tag


newtype Roar r a b = Roar { runRoar :: (r -> a) -> (r -> b) }
  deriving stock Functor

instance Applicative (Roar r a) where
  pure a = Roar $ \ _ _ -> a
  (<*>) (Roar f) (Roar g) = Roar $ \ra r -> f ra r (g ra r)

instance Monad (Roar r a) where
  (>>=) (Roar g) f = Roar $ \ fra r -> runRoar (f $ g fra r) fra r

instance (CoArbitrary a, CoArbitrary r, Arbitrary r, Arbitrary b) => Arbitrary (Roar r a b) where
  arbitrary = Roar <$> arbitrary

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
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance SymmetricProduct (Roar r) where
  swap = Roar (\ f r -> swap $ f r)
  {-# INLINE swap #-}
  reassoc = Roar (\ f r -> reassoc $ f r)
  reassoc' = Roar (\ f r -> reassoc' $ f r)

instance MonoidalProduct (Roar r) where
  first' (Roar f) = Roar $ \rac r ->
     (f (fst . rac) r, snd $ rac r)
  {-# INLINE first' #-}
  second' (Roar f) = Roar $ \rac r ->
     (fst $ rac r, f (snd . rac) r)
  {-# INLINE second' #-}

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
    let getLeft t = either id undefined $ rac t
     in either (const $ Left $ f getLeft r) Right $ rac r
  right (Roar f) = Roar $ \ rac r ->
    let getRight t = either undefined id $ rac t
     in either Left (const $ Right $ f getRight r) $ rac r

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
loop b f tx = \case
  n | n <= 0 -> f ((, b) . tx) 0
  t -> let (_, s) = loop b f tx $ t - 1
        in f ((, s) . tx) t


spike :: Time -> Time -> Bool
spike n t = bool False True $ n == t

type Time = Natural

