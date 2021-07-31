{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Circuitry.Shared where

import           Circuitry.Circuit
import           Circuitry.Embed
import           Circuitry.Graph
import           Circuitry.Primitives
import           Circuitry.Signal
import           Circus.DSL (unifyBits)
import           Circus.Types (Bit (..))
import qualified Clash.Sized.Vector as V
import           Data.Function (fix)
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromJust)
import           Data.Word (Word8)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)


instance Embed (a -> b) where
  type SizeOf (a -> b) = 8


data SomeSignal where
  SomeSignal :: (Embed a, Embed b) => Signal a b -> SomeSignal


sharedMap :: IORef (Map Word8 SomeSignal)
sharedMap = unsafePerformIO $ newIORef mempty
{-# NOINLINE sharedMap #-}

sharedGraphMap :: IORef (Map Word8 ([Bit], [Bit]))
sharedGraphMap = unsafePerformIO $ newIORef mempty
{-# NOINLINE sharedGraphMap #-}


share :: forall a b. (Embed a, Embed b) => Circuit a b -> Circuit () (a -> b)
share c = unsafePerformIO $ do
  ix <- fmap (fromIntegral . length) $ readIORef sharedMap
  modifyIORef' sharedMap $ M.insert ix $ SomeSignal $ c_roar c
  pure
    $ primitive
    $ Circuit (gr ix)
    $ primSignal
    $ const
    $ fmap Just
    $ embed ix
  where
    gr :: Word8 -> Graph () (a -> b)
    gr ix = Graph $ \V.Nil -> do
      a <- synthesizeBits @a
      b <- unGraph (c_graph c) a
      unsafePerformIO $ do
        modifyIORef' sharedGraphMap $ M.insert ix (V.toList a, V.toList b)
        pure $ pure $ V.repeat $ embedBit ix
{-# NOINLINE share #-}


embedBit :: Word8 -> Bit
embedBit = Bit . fromIntegral


eval :: forall a b. (Embed a, Embed b) => Circuit (a -> b, a) b
eval
    = Circuit gr
    $ fix $ \me -> Signal
    $ \v -> unsafePerformIO
    $ do
      let (ref, a) = V.splitAtI v
          share_id = reify $ fromJust $ V.traverse# id ref
      shared <- readIORef sharedMap
      case shared M.! share_id of
        SomeSignal sig -> do
          let (sig', b) = pumpSignal (unsafeCoerce sig :: Signal a b) a
          modifyIORef' sharedMap $ M.insert share_id $ SomeSignal sig'
          pure (me, b)
  where
    gr :: Graph (a -> b, a) b
    gr = Graph $ \v -> do
      let (V.head -> Bit ref, a) = V.splitAtI @8 v
          !ix = fromIntegral @_ @Word8 ref
      unsafePerformIO $ do
        (a', b) <- fmap (M.! ix) $ readIORef sharedGraphMap
        pure $ do
          unifyBits $ M.fromList $ zip (V.toList a) a'
          pure $ V.unsafeFromList b
{-# NOINLINE eval #-}

