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
  AndG :: CircuitF (Bool, Bool) Bool
  NandG ::CircuitF (Bool, Bool) Bool
  OrG  :: CircuitF (Bool, Bool) Bool
  NorG :: CircuitF (Bool, Bool) Bool
  NotG :: CircuitF Bool Bool
  -- Machine :: String -> [String] -> [String] -> Circuit a b -> CircuitF a b
  -- Label :: String -> Circuit a b -> CircuitF a b

deriving instance Show (CircuitF a b)


andGate :: Catalyst r CircuitF (Bool, Bool) Bool
andGate = LiftC AndG

nandGate :: Catalyst r CircuitF (Bool, Bool) Bool
nandGate = LiftC NandG


orGate :: Catalyst r CircuitF (Bool, Bool) Bool
orGate = LiftC OrG

norGate :: Catalyst r CircuitF (Bool, Bool) Bool
norGate = LiftC NorG


notGate :: Catalyst r CircuitF Bool Bool
notGate = LiftC NotG


type Circuit = FreeFunction CircuitF



test :: Circuit ((Bool, Bool), Bool) ((Bool, Bool), Bool)
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
  PortMap _1 = PortRef


compile :: Circuit a b -> PortMap a -> GraphViz (PortMap b)
compile ID i = pure i
compile (Comp cat cat') i = do
  o1 <- compile cat i
  o2 <- compile cat' o1
  pure o2
compile Swap (i1, i2) =
  pure (i2, i1)
compile Reassoc (i1, (i2, i3)) =
  pure ((i1, i2), i3)
compile (First cat) i = undefined
compile (Second cat) i = undefined
compile (Alongside cat cat') x =
  case x of
    (i1, i2) -> do
      o1 <- compile cat i1
      o2 <- compile cat' i2
      pure (o1, o2)
compile (Fanout cat cat') i = undefined
compile Copy i = do
  (inp, out) <- component Point ["i"] ["o1", "o2"]
  undefined
  -- connect i inp
  -- pure out
compile Consume i = undefined
compile Fst (i1, i2) =
  pure i1
compile Snd (i1, i2) =
  pure i2
compile (LiftC (Feedback cat)) i = mdo
  (o, s) <- compile cat (i, s)
  pure o
compile (LiftC AndG) (i1, i2) = do
  ([ai1, ai2], [o]) <- component (Record "and") ["", ""] [""]
  connect i1 ai1
  connect i2 ai2
  pure o
-- compile i (LiftC NandG) = component (Record "nand") ["", ""] [""]
compile (LiftC OrG) (i1, i2) = do
  ([ai1, ai2], [o]) <- component (Record "⦈") ["", ""] [""]
  connect i1 ai1
  connect i2 ai2
  pure o
-- compile i (LiftC NorG) = component (Record "nor") ["", ""] [""]
compile (LiftC NotG) i = do
  ([ai1], [o]) <- component (Record "▷") [""] [""]
  connect i ai1
  pure o
compile z _ = error $ show z


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


test2 :: Circuit Bool Bool
test2 = notGate >>> (feedback $ orGate >>> copy) >>> notGate >>> id

test3 :: Circuit (Bool, Bool) Bool
test3 = feedback $ reassoc' >>> second' norGate >>> norGate >>> copy

reassoc' :: (MonoidalProduct k, SymmetricProduct k) => ((a, b), c) `k` (a, (b, c))
reassoc' = first' swap >>> swap >>> reassoc >>> swap >>> second' swap


clock :: Circuit () Bool
clock = feedback $ snd' >>> notGate >>> copy


spike :: Natural -> Natural -> Bool
spike n t = bool False True $ n == t


