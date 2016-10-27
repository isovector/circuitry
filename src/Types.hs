{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
module Types
    ( C
    , DSL (..)
    , Port (..)
    , DiaID
    , ports
    , compose
    ) where

import Control.Lens
import Control.Monad.Fix
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict (StateT)
import Data.Hashable
import Data.Map (Map)
import qualified Data.Map as M (empty)
import Data.Typeable
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Constrained
import Diagrams.TwoD.Shapes

data DSLState s b n m = DSLState
    { _ports   :: Map (DiaID s, Name) (P2 (Expr s n))
    , _compose :: QDiagram b V2 n m -> QDiagram b V2 n m
    }
makeLenses ''DSLState

instance Default (DSLState s b n m) where
    def = DSLState M.empty id

type C n m = (Hashable n, Semigroup m, RealFrac n, Floating n, Monoid m)

newtype DSL s b n m a = DSL
    { unDSL :: StateT (DSLState s b n m)
                      (Constrained s b n m) a
    }
    deriving ( Functor
             , Applicative
             , Monad
             , MonadState (DSLState s b n m)
             , MonadFix
             )

data Port = In Int
          | Out Int
          | Split
          | Named String
          deriving (Typeable, Ord, Show, Read, Eq)
instance IsName Port

