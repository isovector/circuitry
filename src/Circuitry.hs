{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecursiveDo                #-}

module Circuitry where

import           Control.Arrow (first, second)
import           Control.Monad (forM_)
import           Control.Monad.State.Class
import           Control.Monad.Trans (lift)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State.Strict (StateT, execStateT)
import           Data.Hashable
import           Data.Map.Strict (Map)
import           Data.Maybe (fromJust)
import           Data.Typeable
import           Diagrams.Prelude hiding (trace, showTrace)
import qualified Diagrams.TwoD.Layout.Constrained as C
import           Diagrams.TwoD.Shapes
import           Unsafe.Coerce
import qualified Data.Map.Strict as M

import Circuitry.Backend
import Circuitry.Types

type Circuit' s = Circuit s B Double Any

runCircuit :: (C n m, Show n) => (forall s. Circuit s b n m a) -> QDiagram b V2 n m
-- TODO(sandy): this is probably ok
runCircuit (Circuit dsl) = let c      = execStateT dsl def
                               (s, d) = C.layout $ unsafeCoerce c
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
        modify (over ports $ M.insert (dia, pname) port)
    return dia

withPort :: DiaID s -> Port -> (P2 (C.Expr s n) -> Circuit s b n m a) -> Circuit s b n m a
withPort = ((>>=) .) . getPort

getPort :: DiaID s -> Port -> Circuit s b n m (P2 (C.Expr s n))
getPort c p = gets ((M.! (c, toName (show c, p))) . view ports)

assertSame :: C n m => DiaID s -> Port -> DiaID s -> Port -> Circuit s b n m ()
assertSame c p c' p' = do
  p1 <- getPort c p
  p2 <- getPort c' p'
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
arr a b = afterwards $ connect' headless (first show a) (first show b)
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

