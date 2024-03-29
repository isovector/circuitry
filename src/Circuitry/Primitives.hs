{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Circuitry.Primitives where

import           Circuitry.Category (Category(..), (>>>))
import           Circus.DSL
import qualified Circus.Types as Y
import           Clash.Sized.Vector (Vec(..))
import qualified Clash.Sized.Vector as V
import           Control.Lens ((-~))
import           Control.Monad.Reader (local, asks)
import           Control.Monad.State (StateT(..), get, lift, MonadState (put), runStateT, execStateT)
import qualified Data.Aeson as A
import           Data.Bool (bool)
import           Data.Generics.Labels ()
import qualified Data.Map as M
import           Data.Maybe (isNothing)
import qualified Data.Text as T
import           Debug.Trace (trace)
import           GHC.TypeLits
import           Prelude hiding ((.), id, sum)
import           Circuitry.Circuit
import           Circuitry.Embed
import           Circuitry.Graph
import           Circuitry.Signal (Signal (..), primSignal)
import           Unsafe.Coerce (unsafeCoerce)


primitive :: Circuit a b -> Circuit a b
primitive = id


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


pullDown :: Circuit Bool Bool
pullDown = primitive $ Circuit gr $ Signal $ \(v :> Nil) ->
    (c_roar pullDown, maybe (Just False) Just v :> Nil)
  where
    gr :: Graph Bool Bool
    gr = Graph $ \(v :> Nil) -> do
      vcc <- freshBit
      addCell $ Y.mkCell (Y.CellGeneric "$gnd") $
        M.singleton "A" (Y.Output, [vcc])
      addCell $ Y.mkCell' (Y.CellGeneric "$r") (M.singleton "value" "10k") $
        M.fromList
          [ ("B", (Y.Input, [vcc]))
          , ("A", (Y.Output, [v]))
          ]
      pure $ v :> Nil

pullUp :: Circuit Bool Bool
pullUp = primitive $ Circuit gr $ Signal $ \(v :> Nil) ->
    (c_roar pullDown, maybe (Just True) Just v :> Nil)
  where
    gr :: Graph Bool Bool
    gr = Graph $ \(v :> Nil) -> do
      vcc <- freshBit
      addCell $ Y.mkCell (Y.CellGeneric "$vcc") $
        M.singleton "A" (Y.Output, [vcc])
      addCell $ Y.mkCell' (Y.CellGeneric "$r") (M.singleton "value" "10k") $
        M.fromList
          [ ("A", (Y.Input, [vcc]))
          , ("B", (Y.Output, [v]))
          ]
      pure $ v :> Nil


swap :: forall a b. (OkCircuit a, OkCircuit b) => Circuit (a, b) (b, a)
swap =
  primitive $ raw $ Circuit gr $ primSignal $ \v ->
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
(***) l r = primitive $ raw $ Circuit gr $ go (c_roar l) (c_roar r)
  where
    gr :: Graph (Vec (SizeOf (a, b)) Bool) (Vec (SizeOf (a', b')) Bool)
    gr = Graph $ \i -> do
      let (i1, i2) = V.splitAtI i
      o1 <- unGraph (c_graph l) i1
      o2 <- unGraph (c_graph r) i2
      pure $ o1 V.++ o2

    go :: Signal a a' -> Signal b b' -> Signal (Vec (SizeOf (a, b)) Bool) (Vec (SizeOf (a', b')) Bool)
    go k1 k2 = Signal $ \i ->
      let (i1, i2) = V.splitAtI i
          (s1, o1) =  pumpSignal k1 i1
          (s2, o2) =  pumpSignal k2 i2
      in (go s1 s2, o1 V.++ o2)


consume :: OkCircuit a => Circuit a ()
consume = primitive $ raw $ Circuit (Graph $ const $ pure Nil) $ primSignal $ const Nil


coerceC
    :: ( Embed a, Embed b1, Embed c, Embed b2
       , SizeOf b2 ~ SizeOf c
       , SizeOf a ~ SizeOf b1
       )
    => Circuit b1 b2
    -> Circuit a c
coerceC c = unsafeReinterpret . c . unsafeReinterpret


unsafeReinterpret :: (OkCircuit a, OkCircuit b, SizeOf a ~ SizeOf b) => Circuit a b
unsafeReinterpret = raw id


copy :: forall a. OkCircuit a => Circuit a (a, a)
copy = replicateC >>> unsafeReinterpret
  -- where
  --   gr :: Graph (Vec (SizeOf a) Bool) (Vec (SizeOf (a, a)) Bool)
  --   gr = Graph $ \i -> pure $ i V.++ i


replicateC :: forall m a. (KnownNat m, OkCircuit a) => Circuit a (Vec m a)
replicateC = primitive $ raw $ Circuit gr $ primSignal $ V.concat . V.repeat
  where
    gr = Graph $ pure . V.concat . V.repeat


fst' :: (OkCircuit a, OkCircuit b) => Circuit (a, b) a
fst' = primitive $ raw $ Circuit (Graph $ pure . V.takeI) $ primSignal V.takeI


constantName :: (Show a, Reify a) => a -> GraphM String
constantName a = do
  asks ro_unpack_constants >>= pure . \case
    False -> show a
    True -> fmap (bool '0' '1') $ V.toList $ embed a


pad
    :: forall m n a
     . (Show a, Reify a, KnownNat m, KnownNat n, m <= n)
    => a
    -> Circuit (Vec m a) (Vec n a)
pad a = primitive
       $ Circuit gr
       $ primSignal
       $ \v -> v V.++ V.concat (V.repeat @(n - m) $ fmap Just $ embed a)
  where
    gr :: Graph (Vec m a) (Vec n a)
    gr = Graph $ \v -> do
      v2 <- synthesizeBits @(Vec (n - m) a)
      name <- constantName a
      addCell $
        Y.Cell Y.CellConstant
          (M.singleton (Y.Width "Y") $ V.length v2)
          (M.singleton "value" $ A.String $ T.pack name)
          (M.singleton "Y" Y.Output)
          (M.singleton "Y" $ V.toList v2)
      pure $ v V.++ v2



nandGate :: Circuit (Bool, Bool) Bool
nandGate
  = primitive
  $ Circuit (binaryGateDiagram Y.CellNand)
  $ Signal $ \(mb1 :> mb2 :> Nil) ->
    (c_roar nandGate, (:> Nil) $ fmap not $
      case (mb1, mb2) of
        (Just b1, Just b2) -> Just $ b1 && b2
        (Just b1, Nothing) -> Just b1
        (Nothing, Just b2) -> Just b2
        (Nothing, Nothing) -> Nothing
    )


tribuf :: Circuit (Bool, Bool) Bool
tribuf = primitive $ Circuit gr $ Signal $ \(a :> en :> Nil) ->
    (c_roar tribuf, (en >>= bool Nothing a) :> Nil)
  where
    gr :: Graph (Bool, Bool) Bool
    gr = Graph $ \(Cons i1 (Cons i2 Nil)) -> do
      out <- freshBit
      addCell $ Y.mkCell Y.CellTribuf $ M.fromList
        [  ("A",  (Y.Input, [i1]))
        ,  ("EN", (Y.Input, [i2]))
        ,  ("Y",  (Y.Output, [out]))
        ]
      pure $ Cons out Nil

------------------------------------------------------------------------------
-- | NOTE: Leads to undefined behavior in the circuit world if more than one of
-- the incoming bits are not Z.
unsafeShort :: Circuit (Vec n Bool) Bool
unsafeShort = primitive $ Circuit gr $ Signal $ \a ->
    (c_roar unsafeShort, V.foldr merge Nothing a :> Nil)
  where
    gr :: Graph (Vec n Bool) Bool
    gr = Graph $ \bin -> do
      o <- freshBit
      let subst = M.fromList $ zip (V.toList bin) $ repeat o
      unifyBits subst
      pure $ o :> Nil

    merge :: Maybe Bool -> Maybe Bool -> Maybe Bool
    merge (Just _) (Just _) = error "unsafeShort: got values at the same time"
    merge (Just a) _ = Just a
    merge Nothing a = a



mapFoldVC
    :: forall n a b r
     . (KnownNat n, OkCircuit a, OkCircuit b, OkCircuit r)
    => Circuit (a, r) (b, r)
    -> Circuit (Vec n a, r) (Vec n b, r)
mapFoldVC c = Circuit gr go
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
zipVC = primitive $ Circuit gr $ primSignal func
  where
    func :: Vec (n * SizeOf a + n * SizeOf b) x -> Vec (n * (SizeOf a + SizeOf b)) x
    func i =
      let (a, b) = V.splitAtI @(n * SizeOf a) i
          as = V.unconcatI @n a
          bs = V.unconcatI @n b
       in V.concatMap (\(v1, v2) -> v1 V.++ v2) $ V.zip as bs

    gr :: Graph (Vec n a, Vec n b) (Vec n (a, b))
    gr = Graph $ pure. func


cloneV :: forall n r. (KnownNat n, Embed r) => Circuit r (Vec n r)
cloneV = primitive $ Circuit gr $ primSignal $ V.concat . V.repeat
  where
    gr :: Graph r (Vec n r)
    gr = Graph $ \i -> do
      pure $ V.concat $ V.repeat i


fixC
    :: forall s a b
     . (Reify s, Embed a, Embed b)
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
      pure $ unifyBitsPure subst b

transposeV
    :: forall m n a
     . (KnownNat n, KnownNat m, KnownNat (SizeOf a), Embed a)
    => Circuit (Vec m (Vec n a)) (Vec n (Vec m a))
transposeV = primitive $ Circuit gr $ primSignal $ \i ->
      let v' = fmap (V.unconcatI @n) $ V.unconcatI @m i
       in V.concat $ V.concat $ V.transpose v'
  where
    gr :: Graph (Vec m (Vec n a)) (Vec n (Vec m a))
    gr = Graph $
      \i -> do
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


crossV
    :: forall n
     . KnownNat n
    => Circuit (Bool, Bool) Bool
    -> Circuit (Vec n Bool) (Vec (2 ^ n) Bool)
crossV c = Circuit gr $ primSignal V.reverse >>> go
  where
    go :: forall n'. KnownNat n' => Signal (Vec n' Bool) (Vec (2 ^ n') Bool)
    go = Signal $ \case
        Nil -> (go, Cons (Just True) Nil)
        vin@(Cons _ _) ->
          pumpSignal (update go $ V.repeat $ c_roar c) vin

    update
        :: forall n'
         . Signal (Vec n' Bool) (Vec (2 ^ n') Bool)
        -> Vec (2 ^ (n' + 1)) (Signal (Bool, Bool) Bool)
        -> Signal (Vec (n' + 1) Bool) (Vec (2 ^ (n' + 1)) Bool)
    update sind vsig = Signal $ \i ->
      let (b, vin) = V.splitAtI i
          b_not = fmap (fmap not) b
          (sres, vres) = pumpSignal sind vin
          vl = fmap ((b_not V.++) . flip Cons Nil) vres
          vr = fmap ((b V.++) . flip Cons Nil) vres
          (sout, vout) = V.unzip $ V.zipWith pumpSignal vsig  $ vl V.++ vr
       in (update sres sout, V.concat vout)

    gr :: forall m. KnownNat m => Graph (Vec m Bool) (Vec (2 ^ m) Bool)
    gr = Graph $ \case
        Nil -> do
          o <- unGraph (c_graph $ pad True) Nil
          pure o
        Cons b Nil -> do
          bnot <- unGraph (c_graph notGate) $ Cons b Nil
          pure $ V.reverse $ b :> bnot
        Cons b vin -> do
          bnot <- fmap V.head $ unGraph (c_graph notGate) $ Cons b Nil
          (vout :: Vec (2 ^ (m - 1)) Y.Bit) <- unGraph gr $ vin
          fmap V.concat $ flip V.traverse# vout $ \vb -> do
            vl <- unGraph (c_graph c) $ Cons bnot $ Cons vb Nil
            vr <- unGraph (c_graph c) $ Cons b $ Cons vb Nil
            pure $ vl V.++ vr


notGate :: Circuit Bool Bool
notGate
  = gateDiagram (unaryGateDiagram Y.CellNot)
  $ copy >>> nandGate


------------------------------------------------------------------------------
-- | Too slow to run real world physics? JET STREAM IT, BABY.
-- This will fall back to the direct implementation if any of the wires are Z.
shortcircuit :: (Reify a, Reify b) => (a -> b) -> Circuit a b -> Circuit a b
shortcircuit f c = Circuit (c_graph c) $ Signal $ \ma ->
  case V.traverse# id ma of
    Just a  -> (c_roar $ shortcircuit f c, fmap Just $ embed $ f (reify a) )
    Nothing -> pumpSignal (c_roar c) ma


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
     . (Embed a, Embed c)
    => Y.CellType
    -> Graph a c
unaryGateDiagram = unaryGateDiagram' "A"

unaryGateDiagram'
    :: forall a c
     . (Embed a, Embed c)
    => Y.PortName
    -> Y.CellType
    -> Graph a c
unaryGateDiagram' p ty = Graph $ \a -> do
  c <- synthesizeBits @c
  addCell $
    Y.Cell
      ty
      (M.singleton (Y.Width p) $ V.length a)
      mempty
      (M.fromList
        [ (p, Y.Input)
        , ("Y", Y.Output)
        ])
      (M.fromList
        [ (p, V.toList a)
        , ("Y", V.toList c)
        ])
  pure c

binaryGateDiagram
    :: forall a b c
     . (Embed a, Embed b, Embed c)
    => Y.CellType
    -> Graph (a, b) c
binaryGateDiagram ty = Graph $ \i -> do
  let (a, b) = V.splitAtI @(SizeOf a) i
  c <- synthesizeBits @c
  addCell $ Y.mkCell ty $ M.fromList
    [ ("A", (Y.Input, V.toList a))
    , ("B", (Y.Input, V.toList b))
    , ("Y", (Y.Output, V.toList c))
    ]
  pure c


traceC :: forall a. (Reify a, Show a) => String -> Circuit a a
traceC n
  = primitive
  $ Circuit id
  $ primSignal
  $ \v -> trace (n <> ": " <> show (fmap (reify @a) $ V.traverse# id v)) v


bypassing :: forall a b. Embed b => Circuit a b -> Circuit a b
bypassing c = Circuit (c_graph c) $ go $ c_roar c
  where
    go :: Signal a b -> Signal a b
    go c0 = Signal $ \v ->
      case any isNothing $ V.toList v of
        True -> (go c0, V.repeat Nothing)
        False ->
          let (s, v') = pumpSignal c0 v
           in (go s, v')

