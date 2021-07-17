module Design where

import Data.Bool (bool)
import Data.Char (isAlphaNum)
import Data.List (group)
import Data.Maybe (fromMaybe, isJust)
import Prelude hiding ((.), id)
import System.Process (callProcess)
import Circuitry.Machinery


__design
    :: (Embed a, Embed b, SeparatePorts a, SeparatePorts b)
    => (String, [String], [(String, String)])
    -> String
    -> String
    -> Circuit a b
    -> IO ()
__design (name, _, kvs) txt hash c = do
  let fp = hash <> ".png"
      label = fromMaybe txt $ lookup "label" kvs
      figname = bool name ("fig:" <> __makeFigName label)  $ name == ""
      expand_gates = isJust $ lookup "gates" kvs
      depth = maybe 0 read $ lookup "depth" kvs

  writeFile "/tmp/output.json"
    $ renderModuleString
    $ getGraph (RenderOptions expand_gates False depth) c
  callProcess "netlstsvg"
    [ "/tmp/output.json"
    , "-o"
    , fp
    , "--skin"
    , "~/prj/circuitry/skin.svg"
    ]

  putStrLn $
    mconcat ["![", label, "](", fp, "){#", figname , "}"]


__makeFigName :: String -> String
__makeFigName
    = concatMap (\x -> bool x (take 1 x) $ take 1 x == "_")
    . group
    . fmap go
  where
    go c | isAlphaNum c = c
    go _ = '_'

