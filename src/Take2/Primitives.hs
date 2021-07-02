{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE MagicHash            #-}
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
import Control.Monad.Reader (ask, local)


primitive :: Circuit a b -> Circuit a b
primitive = id


timeInv :: (a -> b) -> Signal a b
timeInv = primSignal
{-# INLINE timeInv #-}

coerceCircuit
    :: (Coercible a a', Coercible b b', SizeOf a ~ SizeOf a', SizeOf b ~ SizeOf b')
    => Circuit a b
    -> Circuit a' b'
coerceCircuit (Circuit gr c) =
  Circuit (coerceGraph gr) (timeInv coerce >>> c >>> timeInv coerce)


raw
    :: forall a b
     . (OkCircuit a, OkCircuit b)
    => Circuit (Vec (SizeOf a) Bool) (Vec (SizeOf b) Bool)
    -> Circuit a b
raw c = Circuit (coerceGraph $ c_graph c) $
  Signal $ \a ->
    let (sf, sb) = pumpSignal (c_roar c) $ embed a
     in (dimap embed reify sf, reify sb)


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
      addNamedCell (Y.CellName $ T.pack $ show a) $
        Y.Cell Y.CellConstant
          (M.singleton (Y.Width "Y") $ V.length v2)
          (M.singleton "value" $ A.String $ T.pack $ show a)
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




mapFoldVC
    :: forall n a b r
     . (KnownNat n, OkCircuit a, OkCircuit b, OkCircuit r)
    => Circuit (a, r) (b, r)
    -> Circuit (Vec n a, r) (Vec n b, r)
mapFoldVC c = primitive $ Circuit gr $
  timeInv
    ( ((\(v, r) ->
        case v of
          Nil -> Left (Nil, r)
          Cons a v' -> Right $ ((a, r), v')
      ) :: (Vec n a, r) -> Either (Vec n b, r) ((a, r), Vec (n - 1) a))
    )
  >>> Category.right
        ( Category.first' (c_roar c)
      >>> Category.reassoc'
      >>> Category.second'
          ( Category.swap
        >>> Category.second' Category.copy
        >>> Category.reassoc
        >>> Category.first'
            ((Signal (\a ->
              case unsafeSatisfyGEq1 @(n - 1) of
                Dict -> pumpSignal (c_roar $ mapFoldVC c) a
              ) :: Signal (Vec (n - 1) a, r) (Vec (n - 1) b, r)
            )
        >>> Category.fst'
            )
          )
      >>> Category.reassoc
      >>> Category.first' (timeInv $ uncurry Cons)
        )
  >>> Category.unify
  where
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
     . (KnownNat n, KnownNat (SizeOf a), KnownNat (SizeOf b))
    => Circuit (Vec n a, Vec n b) (Vec n (a, b))
zipVC = primitive $ Circuit gr $ timeInv $ uncurry V.zip
  where
    gr :: Graph (Vec n a, Vec n b) (Vec n (a, b))
    gr = Graph $ \i -> do
      let (a, b) = V.splitAtI @(n * SizeOf a) i
          as = V.unconcatI @n a
          bs = V.unconcatI @n b
      pure $ V.concatMap (\(v1, v2) -> v1 V.++ v2) $ V.zip as bs


cloneV :: forall n r. KnownNat n => Circuit r (Vec n r)
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
    go s k = Signal $ \a ->
      let (k', (b, s')) = pumpSignal k (a, s)
      in (go s' k', b)

    gr :: Graph a b
    gr = Graph $ \v -> do
      s <- synthesizeBits @s
      o <- unGraph (c_graph k0) (v V.++ s)
      let (b, s') = V.splitAtI o
          subst = M.fromList $ V.toList $ V.zip s s'
      unifyBits subst
      pure $ unifyBitsImpl subst b



foldVC :: forall n a b. (KnownNat n, Embed a, Embed b) => Circuit (a, b) b -> Circuit (Vec n a, b) b
foldVC c = primitive $ Circuit gr $ foldSig $ c_roar c
  where
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

-- NOTE(sandy): this thing will pump the first arg for every element in the
-- vector. seems reasonable, but also that it can't possibly clock --- but
-- maybe that's to be expected?
foldSig :: Signal (a, b) b -> Signal (Vec n a, b) b
foldSig (Signal f) = Signal $ \(v, b) ->
  case v of
    Nil -> (timeInv snd, b)
    Cons a v' ->
      let (sa, b') = f (a, b)
          (sv, b'') = pumpSignal (foldSig sa) (v', b')
       in (lmap (first V.dropI) sv, b'')


------------------------------------------------------------------------------
-- | Too slow to run real world physics? JET STREAM IT, BABY.
shortcircuit :: (a -> b) -> Circuit a b -> Circuit a b
shortcircuit f c = Circuit (c_graph c) $ timeInv f

diagrammed :: Graph a b -> Circuit a b -> Circuit a b
diagrammed g c = c
  { c_graph = Graph $ \v -> do
      depth <- ask
      case depth > 0 of
        True -> local (subtract 1) $ unGraph (c_graph c) v
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

