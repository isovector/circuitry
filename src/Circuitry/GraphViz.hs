{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}

module Circuitry.GraphViz
  ( GraphViz
  , runGraphViz
  , component
  , connect
  , GraphVizCmd(..)
  , Shape (..)
  , PortRef (..)
  ) where


import Control.Monad.State
import Control.Monad.Writer
import Data.List (intercalate)


newtype GraphViz a = GraphViz
  { unGraphViz :: StateT Int (Writer [GraphVizCmd]) a
  }
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadState Int
    , MonadWriter [GraphVizCmd]
    , MonadFix
    )

instance MonadFail GraphViz where
  fail = error

data GraphVizCmd
  = Node Component
  | Edge PortRef PortRef
  | Raw String
  deriving (Eq, Ord)

instance Show GraphVizCmd where
  show (Node com) = show com <> ";"
  show (Edge pr pr') = mconcat
    [ show pr
    , " -> "
    , show pr'
    , ";"
    ]
  show (Raw s) = s


data Compass = East | West
 deriving (Eq, Ord, Enum, Bounded)

instance Show Compass where
  show East = "e"
  show West = "w"

data PortRef = PortRef
  { pr_cid :: ComponentId
  , pr_pid :: PortId
  , pr_io  :: Compass
  }
  deriving (Eq, Ord)


instance Show PortRef where
  show pr = mconcat
    [ show $ pr_cid pr
    , ":"
    , show $ pr_pid pr
    , ":"
    , show $ pr_io pr
    ]


newtype PortId = PortId
  { getPortId ::  Int
  }
  deriving stock (Eq, Ord)
  deriving newtype Num

instance Show PortId where
  show = mappend "p" . show . getPortId

newtype ComponentId = ComponentId
  { getComponentId :: Int
  }
  deriving stock (Eq, Ord)
  deriving newtype Num

instance Show ComponentId where
  show = mappend "c" . show . getComponentId

data Shape
  = Record String
  | Point
  | Wire
  | Ground
  deriving (Eq, Ord, Show)

layoutShape :: Shape -> [Port] -> [Port] -> String
layoutShape (Record str) inp out = mconcat
  [ "[label=\"{{"
  , mkRecord inp
  , "}|"
  , str
  , "|{"
  , mkRecord out
  , "}}\"]"
  ]
layoutShape Point _ _ = "[shape=point]"
layoutShape Wire _ _ = "[label=\" \", style=invis]"
layoutShape Ground _ _ = "[label=\"\", shape=invhouse]"


data Port = Port
  { p_id :: PortId
  , p_name :: String
  }
  deriving (Eq, Ord)

instance Show Port where
  show p = mconcat
    [ "<"
    , show $ p_id p
    , ">"
    , p_name p
    ]


data Component = Component
  { c_id     :: ComponentId
  , c_shape :: Shape
  , c_inputs :: [Port]
  , c_outputs :: [Port]
  }
  deriving (Eq, Ord)

instance Show Component where
  show Component{..} =
    mappend (show c_id) $
      layoutShape c_shape c_inputs c_outputs

mkRecord :: [Port] -> String
mkRecord = intercalate "|" . fmap show


fresh :: MonadState Int m => m Int
fresh = get <* modify (+ 1)


mkPort :: MonadState Int m => String -> m Port
mkPort nm =
  Port
    <$> fmap PortId fresh
    <*> pure nm


mkComponent
    :: MonadState Int m
    => Shape
    -> [String]
    -> [String]
    -> m Component
mkComponent sym ins outs =
  Component
    <$> fmap ComponentId fresh
    <*> pure sym
    <*> traverse mkPort ins
    <*> traverse mkPort outs


component
    :: Shape
    -> [String]
    -> [String]
    -> GraphViz ([PortRef], [PortRef])
component sym ins outs = do
  c <- mkComponent sym ins outs
  let cid = c_id c
      mkRef io x = PortRef cid (p_id x) io
  tell $ pure $ Node c
  pure ( fmap (mkRef West) $ c_inputs c
       , fmap (mkRef East) $ c_outputs c
       )


connect
    :: PortRef
    -> PortRef
    -> GraphViz ()
connect inp = tell . pure . Edge inp


intro :: String
intro = unlines
  [ "digraph G {"
  , "graph [rankdir=LR, splines=spline];"
  , "node [shape=record];"
  , "edge [arrowhead=none];"
  ]

outro :: String
outro = unlines
  [ "}"
  ]


runGraphViz :: GraphViz () -> String
runGraphViz
  = (intro <>)
  . (<> outro)
  . unlines
  . fmap show
  . snd
  . runWriter
  . flip evalStateT 0
  . unGraphViz

