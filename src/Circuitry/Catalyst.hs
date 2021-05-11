{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
module Circuitry.Catalyst where

import Control.Category
import Control.Category.Cartesian
import Control.Category.Free
import Control.Category.Monoidal
import Control.Category.Recursive
import Prelude hiding (id, (.))
import Algebra.Heyting
import Diagrams.Size

import Control.Monad
import qualified Circuitry.Misc as C
import qualified Circuitry.Gates as C
import qualified Circuitry.Types as C
import qualified Circuitry as C
import qualified Diagrams.TwoD.Layout.Constrained as DC
import Circuitry.Backend
import Data.Semigroup (Any)
import Diagrams.Backend.SVG
import Data.Foldable (for_)
import Debug.Trace (traceM)
import Algebra.Lattice
import Diagrams.Prelude (Name, toName, scale)
import Data.Maybe (listToMaybe)
import Data.Typeable (Typeable)
import Data.Function (fix)
import qualified Circuitry.Machinery as C


data CircuitF a b where
  AndG :: Heyting a => CircuitF (a, a) a
  OrG  :: Heyting a => CircuitF (a, a) a
  NotG :: Heyting a => CircuitF a a
  Machine :: String -> [String] -> [String] -> Everything a b -> CircuitF a b
  Label :: String -> Everything a b -> CircuitF a b

deriving instance Show (CircuitF a b)


andGate :: Heyting a => Catalyst r CircuitF (a, a) a
andGate = LiftC AndG


orGate :: Heyting a => Catalyst r CircuitF (a, a) a
orGate = LiftC OrG


notGate :: Heyting a => Catalyst r CircuitF a a
notGate = LiftC NotG

labeled :: String -> Everything a b -> Everything a b
labeled s = LiftC . Label s

machine :: String -> [String] -> [String] -> Everything a b -> Everything a b
machine s is os = LiftC . Machine s is os


type Everything a b = FreeFunction CircuitF a b a b



test :: Heyting a => Everything ((a, a), a) ((a, a), a)
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




compile :: Everything i o -> C.Circuit s B Double Any InputOutput
compile ID = getIO =<< C.liftDia C.input
compile (Comp cat cat') = do
  io1 <- compile cat
  io2 <- compile cat'

  for_ (zip (ioOutput io1) (ioInput io2)) $ \(p1, p2) -> do
    C.assertSame' p1 p2

  pure $ InputOutput (ioInput io1) (ioOutput io2)
-- compile Swap = _
-- compile Reassoc = _
-- compile SwapE = _
-- compile ReassocE = _
-- compile (First cat) = _
-- compile (Second cat) = _

compile (Alongside cat cat') = do
  io1 <- compile cat
  io2 <- compile cat'
  let is = listToMaybe $ zip (reverse (ioInput io1)) (ioInput io2)
      os = listToMaybe $ zip (reverse (ioOutput io1)) (ioOutput io2)

  for_ is $ \(n1, n2) -> do
    p1 <- C.getPort' n1
    p2 <- C.getPort' n2
    C.above p1 p2

  for_ os $ \(n1, n2) -> do
    p1 <- C.getPort' n1
    p2 <- C.getPort' n2
    C.above p1 p2



  pure $ io1 <> io2
-- compile (Fanout cat cat') = _
-- compile (Left' cat) = _
-- compile (Right' cat) = _
-- compile (EitherOf cat cat') = _
-- compile (Fanin cat cat') = _
compile Copy = do
  c <- getIO =<< C.liftDia C.con'
  inp <- getIO =<< C.liftDia C.wire
  down <- getIO =<< (C.liftDia $ scale 2 <$> C.vwire)
  connect inp c
  connect c down
  pure $ InputOutput (ioInput inp) $ ioOutput c <> ioOutput down

-- compile Consume = _
-- compile Fst = _
-- compile Snd = _
-- compile InjectL = _
-- compile InjectR = _
-- compile Unify = _
-- compile Tag = _
-- compile (RecurseL cat) = _
-- compile (RecurseR cat) = _
compile (FixL cat) = do
  io <- compile cat
  let is = listToMaybe $ zip (reverse (ioInput io)) (reverse $ ioOutput io)
  for_ is $ uncurry C.arr'
  pure $ InputOutput (take 1 $ ioInput io) (take 1 $ ioOutput io)


-- compile (FixR cat) = _
compile (LiftC AndG) = getIO =<< C.liftDia C.andGate
compile (LiftC OrG)  = getIO =<< C.liftDia C.orGate
compile (LiftC NotG) = getIO =<< C.liftDia C.notGate
compile (LiftC (Machine s is os c)) = getIO =<< (C.liftDia $ C.machine is os s)
compile (LiftC (Label s c)) = do
  x <- compile c
  C.afterwards $ C.labeled s
  pure x
compile x = error $ show x

connect :: InputOutput -> InputOutput -> C.Circuit s B Double Any ()
connect io1 io2 = do
  let ps = listToMaybe $ zip (ioOutput io1) (ioInput io2)
  for_ ps $ uncurry C.assertSame'


-- ```{#simple}
-- circuit = labeled "Hold" $ runCircuit $ void $ do
--   or <- liftDia orGate
--   c <- liftDia con
--   input <- liftDia wire
--   done <- liftDia wire
--   orOut <- liftDia wire
--   orDown <- liftDia $ scale 2 <$> vwire
--   assertSame or (In 0) input (Out 0)
--   assertSame or (Out 0) orOut (In 0)
--   assertSame orOut (Out 0) orDown (In 0)
--   assertSame orOut (Out 0) done (In 0)
--   assertSame c Split orOut (Out 0)
--   b <- aligning bend Split (or, In 1) (orDown, Out 0)
--   arr (b, Split) (or, In 1)
--   arr (b, Split) (orDown, Out 0)
-- ```

getIO :: DC.DiaID s -> C.Circuit s B Double Any InputOutput
getIO n = do
  ps <- C.getPortsFor n
  let mkName = toName . (show n, )
      i = fmap mkName $ filter C.isInPort ps
      o = fmap mkName $ filter C.isOutPort ps
  pure $ InputOutput {ioInput = i, ioOutput = o}


lowerCircuit :: Everything a b -> a -> b
lowerCircuit = runFree $ \ cf x -> case cf of
  AndG -> uncurry (/\) x
  OrG  -> uncurry (\/) x
  NotG -> neg x
  Machine _ _ _ c -> lowerCircuit c x
  Label _ c -> lowerCircuit c x


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

main :: IO ()
main = do
  let d = C.runCircuit $ void $ compile $ test2
  renderSVG "/tmp/test.svg" (dims 500) d


test2 :: Everything Bool Bool
test2 = labeled "test2" $ notGate >>> (fixL $ orGate >>> copy) >>> notGate >>> id

