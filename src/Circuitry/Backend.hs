{-# LANGUAGE OverloadedStrings #-}

module Circuitry.Backend (B, toDataURL) where

import           Data.ByteString as BS
import qualified Data.ByteString.Base64.URL as URL
import           Data.String.Conv
import           Diagrams.Backend.SVG
import           Diagrams.Prelude
import           Graphics.Svg.Core

toDataURL :: Diagram B -> BS.ByteString
toDataURL = (BS.append "data:image/svg+xml;base64,")
          . URL.encode
          . toS
          . renderBS
          . renderDia SVG (SVGOptions (mkWidth 250) Nothing "" [] True)

