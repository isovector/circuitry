module TribufSpec where

import qualified Clash.Sized.Vector as V
import           Data.Bool (bool)
import           Prelude hiding ((.), id, sum)
import           Take2.Computer.Simple
import           Take2.Machinery
import           Test.Hspec
import           Test.Hspec.QuickCheck
import Data.Maybe (fromMaybe)

spec :: Spec
spec = do
  prop "tribuf specification" $ \(v :: Vec 4 Bool) (en :: Bool) ->
    evalCircuit
        tribufAll
        (v, en)
        0
      === bool Nothing (Just v) en

  prop "zip is resiliant" $ \(v1 :: Vec 4 (Maybe Bool)) ->
    evalCircuitTMV
        (zipVC @4 @Bool @Bool)
        (const $ v1 V.++ v1)
        0
      === (V.concat $ V.zipWith (\x y -> x :> y :> Nil) v1 v1)

  prop "short specification" $ \(v1 :: Vec 1 Bool) (v2 :: Vec 1 Bool) (en :: Bool) ->
    evalCircuit
        shortTest
        ((v1, en), (v2, not en))
        0
      === bool (Just v2) (Just v1) en

  prop "short specification2" $ \v ->
    evalCircuitMV
        unsafeShort
        (Nothing :> Nothing :> Just v :> Nothing :> Nil)
        0
      === Just v :> Nil

  prop "pulldown" $ \sig ->
    evalCircuitMV
        pullDown
        (sig :> Nil)
        0
      === Just (fromMaybe False sig) :> Nil

  prop "pullup" $ \sig ->
    evalCircuitMV
        pullUp
        (sig :> Nil)
        0
      === Just (fromMaybe True sig) :> Nil

shortTest :: KnownNat n => Circuit ((Vec n Bool, Bool), (Vec n Bool, Bool)) (Vec n Bool)
shortTest = both tribufAll >>> pointwise (serial >>> unsafeShort)

