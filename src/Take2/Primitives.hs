{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers #-}

module Take2.Primitives where

import           Circuitry.Catalyst (Signal (..), primSignal)
import           Circuitry.Category (Category(..), (>>>))
import qualified Circuitry.Category as Category
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Monad.State (StateT(..), get, lift, MonadState (put), runStateT, execStateT)
import qualified Data.Aeson as A
import           Data.Bifunctor (first)
import           Data.Coerce (Coercible, coerce)
import           Data.Generics.Labels ()
import qualified Data.Map as M
import           Data.Profunctor (dimap, lmap)
import qualified Data.Text as T
import           GHC.TypeLits
import           Prelude hiding ((.), id, sum)
import           Take2.Circuit
import           Take2.Embed
import           Take2.Graph
import           Unsafe.Coerce (unsafeCoerce)
import qualified Yosys as Y
import Control.Monad.Reader (ask, local, asks)
import Control.Lens ((-~))
import Data.Bool (bool)
import Data.Function (fix)


primitive :: Circuit a b -> Circuit a b
primitive = id


timeInv :: (Embed a, Embed b) => (a -> b) -> Signal a b
timeInv = primSignal
{-# INLINE timeInv #-}

coerceCircuit
    :: (Coercible a a', Coercible b b', SizeOf a ~ SizeOf a', SizeOf b ~ SizeOf b', Embed a', Embed a, Embed b', Embed b)
    => Circuit a b
    -> Circuit a' b'
coerceCircuit (Circuit gr c) =
  Circuit (coerceGraph gr) (timeInv coerce >>> c >>> timeInv coerce)


raw
    :: forall a b
     . (OkCircuit a, OkCircuit b)
    => Circuit (Vec (SizeOf a) Bool) (Vec (SizeOf b) Bool)
    -> Circuit a b
raw c = Circuit (coerceGraph $ c_graph c) $ go (c_roar c)
  where
    go k =
      Signal $ \a ->
        let (sf, sb) = pumpSignal k a
         in (go $ sf, sb)
{-# INLINE raw #-}


swap :: forall a b. (OkCircuit a, OkCircuit b) => Circuit (a, b) (b, a)
swap =
  primitive $ raw $ Circuit gr $ timeInv $ \v ->
    let (va, vb) = V.splitAtI @(SizeOf a) v
    in vb V.++ va
  where
    gr :: Graph (Vec (SizeOf (a, b)) Bool) (Vec (SizeOf (b, a)) Bool)
    gr = Graph $ \v -> do
      let (va, vb) = V.splitAtI @(SizeOf a) v
      pure $ vb V.++ va


(***)
    :: forall a b a' b'
     . (OkCircuit a, OkCircuit b, OkCircuit a', OkCircuit b')
    => Circuit a a'
    -> Circuit b b'
    -> Circuit (a, b) (a', b')
(***) l r =
  primitive $ raw $ Circuit gr $
    timeInv V.splitAtI >>> (Category.***) (timeInv reify >>> c_roar l >>> timeInv embed)
                                          (timeInv reify >>> c_roar r >>> timeInv embed)
                       >>> timeInv (uncurry (V.++))
  where
    gr :: Graph (Vec (SizeOf (a, b)) Bool) (Vec (SizeOf (a', b')) Bool)
    gr = Graph $ \i -> do
      let (i1, i2) = V.splitAtI i
      o1 <- unGraph (c_graph l) i1
      o2 <- unGraph (c_graph r) i2
      pure $ o1 V.++ o2


consume :: OkCircuit a => Circuit a ()
consume = primitive $ raw $ Circuit (Graph $ const $ pure Nil) $ timeInv $ const Nil


copy :: forall a. OkCircuit a => Circuit a (a, a)
copy = primitive $ raw $ Circuit gr $ timeInv $ \v -> v V.++ v
  where
    gr :: Graph (Vec (SizeOf a) Bool) (Vec (SizeOf (a, a)) Bool)
    gr = Graph $ \i -> pure $ i V.++ i


fst' :: (OkCircuit a, OkCircuit b) => Circuit (a, b) a
fst' = primitive $ raw $ Circuit (Graph $ pure . V.takeI) $ timeInv V.takeI


constantName :: (Show a, Embed a) => a -> GraphM String
constantName a = do
  asks ro_unpack_constants >>= pure . \case
    False -> show a
    True -> fmap (bool '0' '1') $ V.toList $ embed a


pad
    :: forall m n a
     . (Show a, Embed a, KnownNat m, KnownNat n, m <= n)
    => a
    -> Circuit (Vec m a) (Vec n a)
pad a = primitive $ Circuit gr $ timeInv $ \v -> v V.++ V.repeat @(n - m) a
  where
    gr :: Graph (Vec m a) (Vec n a)
    gr = Graph $ \v -> do
      v2 <- synthesizeBits @(Vec (n - m) a)
      name <- constantName a
      addNamedCell (Y.CellName $ T.pack name) $
        Y.Cell Y.CellConstant
          (M.singleton (Y.Width "Y") $ V.length v2)
          (M.singleton "value" $ A.String $ T.pack name)
          (M.singleton "Y" Y.Output)
          (M.singleton "Y" $ V.toList v2)
      pure $ v V.++ v2



nandGate :: Circuit (Bool, Bool) Bool
nandGate = primitive $ Circuit gr $ timeInv $ not . uncurry (&&)
  where
    gr :: Graph (Bool, Bool) Bool
    gr = Graph $ \(Cons i1 (Cons i2 Nil)) -> do
      o <- freshBit
      addCell $ Y.mkMonoidalBinaryOp Y.CellNand "A" "B" "Y" [i1] [i2] [o]
      pure $ Cons o Nil


tribuf :: Circuit (Bool, Bool) ZBool
tribuf = primitive $ Circuit gr $ timeInv $ \(a, en) -> bool Z (Bool a) en
  where
    gr :: Graph (Bool, Bool) ZBool
    gr = Graph $ \(Cons i1 (Cons i2 Nil)) -> do
      -- NOTE(sandy): we must be careful to not use en_out anywhere in the graph
      en_out <- freshBit
      out <- freshBit
      addCell $ Y.mkMonoidalBinaryOp Y.CellTribuf "A" "EN" "Y" [i1] [i2] [out]
      pure $ Cons en_out $ Cons out Nil

untribuf :: Circuit ZBool Bool
untribuf = primitive $ Circuit gr $ timeInv $ \case
    Bool b -> b
    -- TODO(sandy): don't error here; change the model so we can represent this
    Z -> error "you untribuffed a Z!"
  where
    gr :: Graph ZBool Bool
    gr = Graph $ \(Cons _ a) -> pure a


mapFoldVC
    :: forall n a b r
     . (KnownNat n, OkCircuit a, OkCircuit b, OkCircuit r)
    => Circuit (a, r) (b, r)
    -> Circuit (Vec n a, r) (Vec n b, r)
mapFoldVC c = Circuit gr $ go
  where
    {-# INLINE combine #-}
    {-# INLINE go #-}

    go :: forall n'. KnownNat n' => Signal (Vec n' a, r) (Vec n' b, r)
    go = Signal $ \i ->
      let (vna, r) = V.splitAtI @(SizeOf (Vec n' a)) i
      in case V.unconcatI @n' vna of
            Nil -> (go, r)
            Cons _ _ -> pumpSignal (combine (c_roar c) go) i

    combine
        :: forall n'
        .  KnownNat n'
        => Signal (a, r) (b, r)
        -> Signal (Vec n' a, r) (Vec n' b, r)
        -> Signal (Vec (n' + 1) a, r) (Vec (n' + 1) b, r)
    combine s1 s2 = Signal $ \i ->
      let (vas, r) = V.splitAtI @(SizeOf (Vec (n' + 1) a)) i
          (V.head -> a, va) = V.splitAtI @1 $ V.unconcatI @(n' + 1) vas
          (sbr, vbr) = pumpSignal s1 (a V.++ r)
          (b, r') = V.splitAtI @(SizeOf b) vbr
          (svs, bsr) = pumpSignal s2 $ V.concat va V.++ r'
       in (combine sbr svs, b V.++ V.takeI bsr V.++ r')

    gr :: Graph (Vec n a, r) (Vec n b, r)
    gr = Graph $ \i -> do
      let (va, r0) = V.splitAtI @(n * SizeOf a) i
          vs = V.unconcatI @n va
      (bs :: Vec n (Vec (SizeOf b) Y.Bit) , r')
        <- flip runStateT r0 $ flip V.traverse# vs $ \a ->
            do
              r <- get
              out <- lift $ unGraph (c_graph c) $ a V.++ r
              let (b, r') = V.splitAtI out
              put r'
              pure b
      pure $ V.concat bs V.++ r'


data Dict c where
  Dict :: c => Dict c

unsafeSatisfyGEq1 :: Dict (1 <= n)
unsafeSatisfyGEq1 = unsafeCoerce $ Dict @(1 <= 2)


zipVC
    :: forall n a b
     . (KnownNat n, KnownNat (SizeOf a), KnownNat (SizeOf b), Embed a, Embed b)
    => Circuit (Vec n a, Vec n b) (Vec n (a, b))
zipVC = primitive $ Circuit gr $ timeInv $ uncurry V.zip
  where
    gr :: Graph (Vec n a, Vec n b) (Vec n (a, b))
    gr = Graph $ \i -> do
      let (a, b) = V.splitAtI @(n * SizeOf a) i
          as = V.unconcatI @n a
          bs = V.unconcatI @n b
      pure $ V.concatMap (\(v1, v2) -> v1 V.++ v2) $ V.zip as bs


cloneV :: forall n r. (KnownNat n, Embed r) => Circuit r (Vec n r)
cloneV = primitive $ Circuit gr $ timeInv V.repeat
  where
    gr :: Graph r (Vec n r)
    gr = Graph $ \i -> pure $ V.concatMap V.repeat i


fixC
    :: forall s a b
     . (Embed s, Embed a, Embed b)
    => s
    -> Circuit (a, s) (b, s)
    -> Circuit a b
fixC s0 k0 = primitive . Circuit gr . go s0 $ c_roar k0
  where
    go s k = Signal $ \v ->
      let (k', v') = pumpSignal k (v V.++ fmap Just (embed s))
          (b, ms') = V.splitAtI v'
      in case V.traverse# id ms' of
           Just s' -> (go (reify s') k', b)
           Nothing -> (go s k', b)

    gr :: Graph a b
    gr = Graph $ \v -> do
      s <- synthesizeBits @s
      o <- unGraph (c_graph k0) (v V.++ s)
      let (b, s') = V.splitAtI o
          subst = M.fromList $ V.toList $ V.zip s s'
      unifyBits subst
      pure $ unifyBitsImpl subst b


transposeV
    :: forall m n a
     . (KnownNat n, KnownNat m, KnownNat (SizeOf a), Embed a)
    => Circuit (Vec m (Vec n a)) (Vec n (Vec m a))
transposeV = primitive $ Circuit gr $ timeInv V.transpose
  where
    gr :: Graph (Vec m (Vec n a)) (Vec n (Vec m a))
    gr = Graph $ \i -> do
      let v' = fmap (V.unconcatI @n) $ V.unconcatI @m i
      pure $ V.concat $ V.concat $ V.transpose v'


foldVC :: forall n a b. (KnownNat n, Embed a, Embed b) => Circuit (a, b) b -> Circuit (Vec n a, b) b
foldVC c = Circuit gr $ go
  where
    {-# INLINE combine #-}
    {-# INLINE go #-}

    go :: forall n'. KnownNat n' => Signal (Vec n' a, b) b
    go = Signal $ \i ->
      let (vna, r) = V.splitAtI @(SizeOf (Vec n' a)) i
      in case V.unconcatI @n' vna of
            Nil -> (go, r)
            Cons _ _ -> pumpSignal (combine (c_roar c) go) i

    combine
        :: forall n'
        .  KnownNat n'
        => Signal (a, b) b
        -> Signal (Vec n' a, b) b
        -> Signal (Vec (n' + 1) a, b) b
    combine s1 s2 = Signal $ \i ->
      let (vas, r) = V.splitAtI @(SizeOf (Vec (n' + 1) a)) i
          (V.head -> a, va) = V.splitAtI @1 $ V.unconcatI @(n' + 1) vas
          (sbr, b) = pumpSignal s1 (a V.++ r)
          (svs, b') = pumpSignal s2 $ V.concat va V.++ b
       in (combine sbr svs, b')

    gr :: Graph (Vec n a, b) b
    gr = Graph $ \i -> do
      let (va, r0) = V.splitAtI @(n * SizeOf a) i
          vs = V.unconcatI @n va
      r'
        <- flip execStateT r0 $ flip V.traverse# vs $ \a ->
            do
              r <- get
              r' <- lift $ unGraph (c_graph c) $ a V.++ r
              put r'
      pure r'


------------------------------------------------------------------------------
-- | Too slow to run real world physics? JET STREAM IT, BABY.
shortcircuit :: (Embed a, Embed b) => (a -> b) -> Circuit a b -> Circuit a b
shortcircuit f c = Circuit (c_graph c) $ timeInv f


unobservable :: Graph a b -> Circuit a b -> Circuit a b
unobservable g c = c { c_graph = g }


diagrammed :: Graph a b -> Circuit a b -> Circuit a b
diagrammed g c = c
  { c_graph = Graph $ \v -> do
      depth <- asks ro_depth
      case depth > 0 of
        True -> local (#ro_depth -~ 1) $ unGraph (c_graph c) v
        False -> unGraph g v
  }

gateDiagram :: Graph a b -> Circuit a b -> Circuit a b
gateDiagram g c = c
  { c_graph = Graph $ \v -> do
      unpack <- asks ro_unpack_gates
      case unpack of
        True -> unGraph (c_graph c) v
        False -> unGraph g v
  }


unaryGateDiagram
    :: forall a c
     . (Embed a, SeparatePorts c)
    => Y.CellType
    -> Graph a c
unaryGateDiagram ty = Graph $ \a -> do
  c <- fst <$> separatePorts @c
  addCell $
    Y.Cell
      ty
      (M.singleton (Y.Width "A") $ V.length a)
      mempty
      (M.fromList
        [ ("A", Y.Input)
        , ("Y", Y.Output)
        ])
      (M.fromList
        [ ("A", V.toList a)
        , ("Y", V.toList c)
        ])
  pure c

binaryGateDiagram
    :: forall a b c
     . (Embed a, Embed b, SeparatePorts c)
    => Y.CellType
    -> Graph (a, b) c
binaryGateDiagram ty = Graph $ \i -> do
  let (a, b) = V.splitAtI @(SizeOf a) i
  c <- fst <$> separatePorts @c
  addCell $ Y.mkMonoidalBinaryOp ty "A" "B" "Y" (V.toList a) (V.toList b) (V.toList c)
  pure c

