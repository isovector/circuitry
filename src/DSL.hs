{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module DSL where

import Control.Arrow (first, second)
import Control.Monad (forM_)
import Control.Monad.State.Class
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict (StateT, execStateT)
import Data.Hashable
import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Data.Typeable
import Diagrams.Prelude hiding (trace, showTrace)
import qualified Diagrams.TwoD.Layout.Constrained as C
import Diagrams.TwoD.Shapes
import Unsafe.Coerce
import qualified Data.Map.Strict as M
import Debug.Trace

import Backend
import Types

type DSL' s = DSL s B Double Any

runDSL :: (C n m, Show n) => (forall s. DSL s b n m a) -> QDiagram b V2 n m
-- TODO(sandy): this is probably ok
runDSL (DSL dsl) = let c      = execStateT dsl def
                       (s, d) = C.layout $ unsafeCoerce c
                    in d # view compose s

liftDSL :: (C.Constrained s b n m) a -> DSL s b n m a
liftDSL = DSL . lift

liftDias :: C n m
         => [DiaID s -> QDiagram b V2 n m]
         -> DSL s b n m [DiaID s]
liftDias = mapM liftDia

liftDia :: C n m
        => (DiaID s -> QDiagram b V2 n m)
        -> DSL s b n m (DiaID s)
liftDia f = mdo
    let d = f dia
    dia <- liftDSL $ C.newDia d
    forM_ (fmap fst $ names d) $ \pname -> do
        port <- liftDSL $ findPort dia pname
        modify (over ports $ M.insert (dia, pname) port)
    return dia

withPort :: DiaID s -> Port -> (P2 (C.Expr s n) -> DSL s b n m a) -> DSL s b n m a
withPort = ((>>=) .) . getPort

getPort :: DiaID s -> Port -> DSL s b n m (P2 (C.Expr s n))
getPort c p = gets ((M.! (c, toName (show c, p))) . view ports)

findPort
  :: (IsName nm, Hashable n,
      Semigroup m, RealFrac n, Floating n) =>
     DiaID s -> nm -> C.Constrained s b n m (P2 (C.Expr s n))
findPort d name = C.newPointOn d (location . fromJust . lookupName name)

leftOf :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
        => P2 (C.Expr s n) -> P2 (C.Expr s n) -> DSL s b n m ()
leftOf = (liftDSL .) . C.constrainDir (direction (r2 (1, 0)))

above :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
      => P2 (C.Expr s n) -> P2 (C.Expr s n) -> DSL s b n m ()
above = (liftDSL .) . C.constrainDir (direction (r2 (0, 1)))

spaceH :: (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)
       => n -> DiaID s -> DiaID s-> DSL s b n m ()
spaceH s a b = liftDSL $ do
  spacer <- C.newDia $ strut unitX # scaleX s # alignR
  C.constrainWith hcat [a, spacer]
  C.sameX b spacer

spaceV :: C n m
       => n -> DiaID s -> DiaID s -> DSL s b n m ()
spaceV s a b = liftDSL $ do
  spacer <- C.newDia $ strut unitY # scaleY s # alignB
  C.constrainWith vcat [a, spacer]
  C.sameY b spacer

sameX :: C n m => DiaID s -> DiaID s -> DSL s b n m ()
sameX = (liftDSL .) . C.sameX

sameY :: C n m => DiaID s -> DiaID s -> DSL s b n m ()
sameY = (liftDSL .) . C.sameY

afterwards :: (QDiagram b V2 n m -> QDiagram b V2 n m) -> DSL s b n m ()
afterwards f = modify (over compose (f .))

arr :: (Typeable n, RealFloat n, Renderable (Path V2 n) b)
    => (DiaID s, Port) -> (DiaID s, Port) -> DSL s b n Any ()
arr a b = afterwards $ connect' headless (first show a) (first show b)
  where
    headless = def & arrowHead .~ noHead

