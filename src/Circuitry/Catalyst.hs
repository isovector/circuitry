{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RecursiveDo                #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall                   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Circuitry.Catalyst where

import Algebra.Heyting
import Algebra.Lattice
import Circuitry.GraphViz
import Control.Category
import Control.Category.Cartesian
import Control.Category.Free hiding (FreeFunction)
import Control.Category.Monoidal
import Control.Category.Recursive ( Fixed(..) )
import Control.Monad ( Functor )
import Control.Monad
import Data.Bool (bool)
import Data.Foldable (for_)
import Data.Function (fix)
import Data.Profunctor.Types ( Profunctor(lmap, rmap) )
import Diagrams.Prelude (Name)
import Numeric.Natural (Natural)
import Prelude hiding (id, (.))


type Time = Natural

type FreeFunction c = Catalyst ('Req 'HasCategory 'HasSymmetricProduct 'NoSymmetricSum 'HasMonoidalProduct 'NoMonoidalSum 'HasCartesian 'NoCocartesian 'NoRecursive 'NoFixed) c


data CircuitF a b where
  Feedback :: Heyting s => Circuit (a, s) (b, s) -> CircuitF a b
  AndG :: Heyting a => CircuitF (a, a) a
  NandG :: Heyting a => CircuitF (a, a) a
  OrG  :: Heyting a => CircuitF (a, a) a
  NorG :: Heyting a => CircuitF (a, a) a
  NotG :: Heyting a => CircuitF a a
  -- Machine :: String -> [String] -> [String] -> Circuit a b -> CircuitF a b
  -- Label :: String -> Circuit a b -> CircuitF a b

deriving instance Show (CircuitF a b)


andGate :: Heyting a => Catalyst r CircuitF (a, a) a
andGate = LiftC AndG

nandGate :: Heyting a => Catalyst r CircuitF (a, a) a
nandGate = LiftC NandG


orGate :: Heyting a => Catalyst r CircuitF (a, a) a
orGate = LiftC OrG

norGate :: Heyting a => Catalyst r CircuitF (a, a) a
norGate = LiftC NorG


notGate :: Heyting a => Catalyst r CircuitF a a
notGate = LiftC NotG


type Circuit = FreeFunction CircuitF



test :: Heyting a => Circuit ((a, a), a) ((a, a), a)
test = notGate *** notGate *** notGate


data InputOutput = InputOutput
  { ioInput :: [Name]
  , ioOutput :: [Name]
  }

instance Semigroup InputOutput where
  (<>) (InputOutput nas nas') (InputOutput nas2 nas3)
    = InputOutput {ioInput = nas <> nas2, ioOutput = nas' <> nas3}

instance Monoid InputOutput where
  mempty = InputOutput {ioInput = mempty, ioOutput = mempty}


noCircuitry :: GraphViz ([PortRef], [PortRef])
noCircuitry = component Empty ["i"] ["o"]

type family PortMap t where
  PortMap (a, b) = (PortMap a, PortMap b)
  PortMap _1 = [PortRef]


compile :: PortMap a -> Circuit a b -> GraphViz (PortMap b)
compile i ID = pure i
compile i (Comp cat cat') = do
  o1 <- compile i cat
  o2 <- compile o1 cat'
  pure o2
compile x Swap =
  case x of
    (i1, i2) -> pure (i2, i1)
compile x Reassoc =
  case x of
    (i1, (i2, i3)) -> pure ((i1, i2), i3)
compile i (First cat) = undefined
compile i (Second cat) = undefined
compile x (Alongside cat cat') =
  case x of
    (i1, i2) -> do
      o1 <- compile i1 cat
      o2 <- compile i2 cat'
      pure (o1, o2)
compile i (Fanout cat cat') = undefined
compile i Copy = do
  (inp, out) <- component Point ["i"] ["o1", "o2"]
  undefined
  -- connect i inp
  -- pure out
compile i Consume = undefined
compile x Fst =
  case x of
    (i1, i2) -> pure i1
compile x Snd =
  case x of
    (i1, i2) -> pure i2
compile i (LiftC (Feedback cat)) = mdo
  (o, s) <- compile (i, s) cat
  pure o
compile _ _ = undefined
-- compile i (LiftC AndG) = component (Record "and") ["", ""] [""]
-- compile i (LiftC NandG) = component (Record "nand") ["", ""] [""]
-- compile i (LiftC OrG) = component (Record "⦈") ["", ""] [""]
-- compile i (LiftC NorG) = component (Record "nor") ["", ""] [""]
-- compile i (LiftC NotG) = component (Record "▷") [""] [""]


newtype Roar r a b = Roar { runRoar :: (r -> a) -> (r -> b) }
  deriving stock Functor

instance Profunctor (Roar r) where
  lmap fab (Roar f) = Roar (\ fra -> f (fab . fra))
  rmap fbc (Roar f) = Roar (\ fra -> fbc . f fra)

instance Category (Roar r) where
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


arr :: (a -> b) -> Roar r a b
arr fab = Roar (\ fra r -> fab (fra r))


lowerCircuit :: Circuit a b -> Roar Natural a b
lowerCircuit = runFree $ \case
    AndG -> arr $ uncurry (/\)
    OrG  -> arr $ uncurry (\/)
    NandG -> arr $ neg . uncurry (/\)
    NorG  -> arr $ neg . uncurry (\/)
    NotG -> arr neg
    Feedback k ->
      let f = runRoar $ lowerCircuit k
       in Roar $ \tx t -> fst $ loop f tx t


loop
    :: Heyting s
    => ((Natural -> (x, s)) -> Natural -> (y, s))
    -> (Natural -> x)
    -> Natural
    -> (y, s)
loop f tx 0 = f ((, bottom) . tx) 0
loop f tx t =
  let (_, s) = loop f tx $ t - 1
   in f ((, s) . tx) t





-- ``` {#not_and_not}
-- circuit = labeled "" $ runCircuit $ void $ do
--   notA <- liftDia $ fmap (\x -> (inputWire ||| x) # scale 0.5) notGate
--   and <- liftDia andGate
--   and1i <- getPort and (In 1)
--   not <- liftDia $ fmap (||| inputWire) notGate
--   notAi <- getPort notA (In 0)
--   assertSame and (Out 0) not (In 0)
--   assertSame notA (Out 0) and (In 0)
--   c <- liftDia $ fmap (\x -> (inputWire ||| x) # scale 0.5) bend
--   cp <- getPort c Split

--   leftOf cp and1i
--   above notAi cp
--   arr (c, Split) (and, In 1)
-- ```


feedback :: Heyting s => Circuit (a, s) (b, s) -> Circuit a b
feedback = liftC . Feedback

-- main :: IO ()
-- main = do
--   let d = C.runCircuit $ void $ compile $ test2 @Bool
--   renderSVG "/tmp/test.svg" (dims 500) d


test2 :: Heyting a => Circuit a a
test2 = notGate >>> (feedback $ orGate >>> copy) >>> notGate >>> id

test3 :: Heyting a => Circuit (a, a) a
test3 = feedback $ reassoc' >>> second' norGate >>> norGate >>> copy

reassoc' :: (MonoidalProduct k, SymmetricProduct k) => ((a, b), c) `k` (a, (b, c))
reassoc' = first' swap >>> swap >>> reassoc >>> swap >>> second' swap


clock :: Heyting a => Circuit () a
clock = feedback $ snd' >>> notGate >>> copy


spike :: Natural -> Natural -> Bool
spike n t = bool False True $ n == t


