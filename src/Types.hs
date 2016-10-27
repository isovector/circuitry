{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
module Types
    ( C
    , DSL (..)
    , Port (..)
    , DiaID
    ) where

import Control.Monad.Fix
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict (StateT)
import Data.Hashable
import Data.Map (Map)
import Data.Typeable
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Constrained
import Diagrams.TwoD.Shapes

type C n m = (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)

newtype DSL s b n m a = DSL
    { unDSL :: StateT (Map (DiaID s, Name) (P2 (Expr s n)))
                      (Constrained s b n m) a
    }
    deriving ( Functor
             , Applicative
             , Monad
             , MonadState (Map (DiaID s, Name)
                          (P2 (Expr s n)))
             , MonadFix
             )

data Port = In Int
          | Out Int
          deriving (Typeable, Ord, Show, Read, Eq)
instance IsName Port

