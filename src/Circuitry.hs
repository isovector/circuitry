{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecursiveDo                #-}

module Circuitry where

import           Control.Arrow (first, second)
import           Control.Category
import           Control.Category.Cartesian
import           Control.Category.Free
import           Control.Category.Monoidal
import           Control.Category.Recursive
import           Control.Monad (forM_)
import           Control.Monad.State.Class
import           Control.Monad.Trans (lift)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State.Strict (StateT, execStateT)
import           Data.Hashable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromJust)
import           Data.Typeable
import           Diagrams.Prelude hiding (trace, showTrace)
import qualified Diagrams.TwoD.Layout.Constrained as C
import           Diagrams.TwoD.Shapes
import           Prelude hiding (id, (.))
import           Unsafe.Coerce

import Circuitry.Backend
import Circuitry.Types
import Data.Maybe (mapMaybe)
import Debug.Trace (traceShowId)
import Data.List (sort)

type Circuit' s = Circuit s B Double Any

runCircuit :: (C n m, Show n) => (forall s. Circuit s b n m a) -> QDiagram b V2 n m
-- TODO(sandy): this is probably ok
runCircuit (Circuit dsl) = let c      = execStateT dsl def
                               (s, d) = C.runLayout $ unsafeCoerce c
                            in d # view compose s

liftCircuit :: (C.Constrained s b n m) a -> Circuit s b n m a
liftCircuit = Circuit . lift

liftDias :: C n m
         => [DiaID s -> QDiagram b V2 n m]
         -> Circuit s b n m [DiaID s]
liftDias = mapM liftDia

liftDia :: C n m
        => (DiaID s -> QDiagram b V2 n m)
        -> Circuit s b n m (DiaID s)
liftDia f = mdo
    let d = f dia
    dia <- liftCircuit $ C.newDia d
    forM_ (fmap fst $ names d) $ \pname -> do
        port <- liftCircuit $ findPort dia pname
        modify (over ports $ M.insert pname port)
    return dia

withPort :: DiaID s -> Port -> (P2 (C.Expr s n) -> Circuit s b n m a) -> Circuit s b n m a
withPort = ((>>=) .) . getPort

getPort :: DiaID s -> Port -> Circuit s b n m (P2 (C.Expr s n))
getPort c p = gets ((M.! toName (show c, p)) . view ports)

getPort' :: Name -> Circuit s b n m (P2 (C.Expr s n))
getPort' n = gets ((M.! n) . view ports)

getPortsFor :: DiaID s -> Circuit s b n m [Port]
getPortsFor c = do
  z <- gets $ view ports
  pure
    . sort
    . fmap snd
    . filter ((== show c) . fst)
    . mapMaybe toPort
    . fmap fst
    $ M.toList z

isInPort :: Port -> Bool
isInPort (In _) = True
isInPort _ = False

isOutPort :: Port -> Bool
isOutPort (Out _) = True
isOutPort _ = False


assertSame :: C n m => DiaID s -> Port -> DiaID s -> Port -> Circuit s b n m ()
assertSame c p c' p' = do
  p1 <- getPort c p
  p2 <- getPort c' p'
  liftCircuit $ p1 C.=.= p2

assertSame' :: C n m => Name -> Name -> Circuit s b n m ()
assertSame' n1 n2 = do
  p1 <- getPort' n1
  p2 <- getPort' n2
  liftCircuit $ p1 C.=.= p2

findPort
  :: (IsName nm, Hashable n,
      Semigroup m, RealFrac n, Floating n) =>
     DiaID s -> nm -> C.Constrained s b n m (P2 (C.Expr s n))
findPort d name = C.newPointOn d (location . fromJust . lookupName name)

leftOf :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
        => P2 (C.Expr s n) -> P2 (C.Expr s n) -> Circuit s b n m ()
leftOf = (liftCircuit .) . C.constrainDir (direction (r2 (1, 0)))

above :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
      => P2 (C.Expr s n) -> P2 (C.Expr s n) -> Circuit s b n m ()
above = (liftCircuit .) . C.constrainDir (direction (r2 (0, 1)))

spaceH :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
       => n -> DiaID s -> DiaID s-> Circuit s b n m ()
spaceH s a b = liftCircuit $ do
  spacer <- C.newDia $ strut unitX # scaleX s # alignR
  C.constrainWith hcat [a, spacer]
  C.sameX b spacer

spaceV :: C n m
       => n -> DiaID s -> DiaID s -> Circuit s b n m ()
spaceV s a b = liftCircuit $ do
  spacer <- C.newDia $ strut unitY # scaleY s # alignB
  C.constrainWith vcat [a, spacer]
  C.sameY b spacer

sameX :: C n m => DiaID s -> DiaID s -> Circuit s b n m ()
sameX = (liftCircuit .) . C.sameX

sameY :: C n m => DiaID s -> DiaID s -> Circuit s b n m ()
sameY = (liftCircuit .) . C.sameY

afterwards :: (QDiagram b V2 n m -> QDiagram b V2 n m) -> Circuit s b n m ()
afterwards f = modify (over compose (f .))

arr :: (Typeable n, RealFloat n, Renderable (Path V2 n) b)
    => (DiaID s, Port) -> (DiaID s, Port) -> Circuit s b n Any ()
arr a b = arr' (toName $ first show a) (toName $ first show b)

arr' :: (Typeable n, RealFloat n, Renderable (Path V2 n) b)
    => Name -> Name -> Circuit s b n Any ()
arr' n1 n2 = afterwards $ connect' headless n1 n2
  where
    headless = def & arrowHead .~ noHead

aligning :: C n m
         => (DiaID s -> QDiagram b V2 n m)
         -> Port
         -> (DiaID s, Port)
         -> (DiaID s, Port)
         -> Circuit s b n m (DiaID s)
aligning d p (dx, px) (dy, py) = do
  getPort dx px >>= \p1 ->
    getPort dy py >>= \p2 -> do
      z <- liftDia d
      zp <- getPort z p
      liftCircuit $ do
        C.along yDir [zp, p1]
        C.along xDir [zp, p2]
      return z

type FoundPort s n = P2 (C.Expr s n)

connecting :: C n m => [(DiaID s, Port, Port)] -> Circuit s b n m ()
connecting ((d, _, output):ds@((d', input, _):_)) =
  assertSame d output d' input >> connecting ds
connecting _ = return ()

same :: C n m
     => (DiaID s -> QDiagram b V2 n m)
     -> Port
     -> (DiaID s, Port)
     -> Circuit s b n m (DiaID s)
same d p (x, y) = do
  d' <- liftDia d
  assertSame d' p x y
  return d'

