{-# LANGUAGE OverloadedStrings #-}

module Circuitry.Backend (B, toDataURL) where

import           Data.ByteString as BS
import           Data.String.Conv
import           Diagrams.Backend.SVG
import           Diagrams.Prelude
import           Graphics.Svg.Core

toDataURL :: Diagram B -> BS.ByteString
toDataURL = (BS.append "data:image/svg+xml;utf8,")
          . toS
          . renderBS
          . renderDia SVG (SVGOptions (mkWidth 250) Nothing "" [] True)

