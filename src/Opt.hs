{-# LANGUAGE GADTs, ScopedTypeVariables #-}
module Opt (propOptFun, deadElimOptFun)
  where

import AbsLatte (Ident)
import IR ( Quad(..), Operand(..), BinOp(..), CompOp(..), QFunDef(..))
import Compiler.Hoopl
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set


data Copied = Copied Operand | CTop deriving (Eq)
type PropFact = Map.Map Operand Copied

propLattice :: DataflowLattice PropFact
propLattice = DataflowLattice {
  fact_name = "const var",
  fact_bot = Map.empty,
  fact_join = joinMaps propFactAdd
}
  where
    propFactAdd _ (OldFact old) (NewFact new) =
      case (old, new) of
        (CTop, _) -> (NoChange, CTop)
        (_, CTop) -> (SomeChange, CTop)
        (Copied old, Copied new) | new == old -> (NoChange, Copied new)
                               | otherwise -> (SomeChange, CTop)

initFact :: [Operand] -> PropFact
initFact ops = Map.fromList  [(v, CTop) | v <- ops]

varIsLit :: FwdTransfer (Quad Operand) PropFact
varIsLit = mkFTransfer ft
  where
    ft :: (Quad Operand) e x -> PropFact -> Fact x PropFact
    ft q f = case q of
      QBinOp d op s1 s2 -> Map.insert d CTop f
      QCompOp d op s1 s2 -> Map.insert d CTop f
      QAnd d s1 s2 -> Map.insert d CTop f
      QOr d s1 s2 -> Map.insert d CTop f
      QNeg d s -> Map.insert d CTop f
      QNot d s -> Map.insert d CTop f
      QLoad d s -> Map.insert d CTop f
      QStore d s -> f
      QCopy d s -> Map.insert d (Copied s) f
      QGoto l -> mapSingleton l f
      QGotoBool r l1 l2 -> mkFactBase propLattice
           [(l1, Map.insert r (Copied $ LitInt 1)  f),
            (l2, Map.insert r (Copied $ LitInt 0) f)]
      QParam r -> f
      QCall d l -> Map.insert d CTop f
      QCallExternal d l -> Map.insert d CTop f
      --QPhi d s1 s2 -> Map.insert d CTop f
      QVRet -> mapEmpty
      QRet r -> mapEmpty
      QLabel l -> f
      QAlloca d -> Map.insert d CTop f
      QError -> mapEmpty

propRewrite :: FuelMonad m => FwdRewrite m (Quad Operand) PropFact
propRewrite = mkFRewrite rw
  where
    rw :: FuelMonad m => (Quad Operand) e x -> PropFact -> m (Maybe(Graph (Quad Operand) e x))
    rw q f = return $ case q of
      QBinOp d op s1 s2 -> rewrite2 f (QBinOp d op) s1 s2
      QCompOp d op s1 s2 -> rewrite2 f (QCompOp d op) s1 s2
      QAnd d s1 s2 -> rewrite2 f (QAnd d) s1 s2
      QOr d s1 s2 -> rewrite2 f (QOr d) s1 s2
      QNeg d s -> rewrite1 f (QNeg d) s
      QNot d s -> rewrite1 f (QNot d) s
      QLoad d s -> rewrite1 f (QLoad d) s
      QStore d s -> rewrite1 f (QStore d) s
      QCopy d s -> rewrite1 f (QCopy d) s
      QGotoBool r l1 l2 -> rewriteLast f (\r1 -> QGotoBool r1 l1 l2) r
      QParam r -> rewrite1 f QParam r
      --QPhi d s1 s2 -> rewrite2 f (QPhi d) s1 s2
      QRet r -> rewriteLast f QRet r
      _ -> Nothing
    lp f v = case Map.lookup v f of
      Just (Copied o) -> Just o
      _ -> Nothing
    rewrite2 f con s1 s2 =
      case (lp f s1, lp f s2) of
        (Nothing, Nothing) -> Nothing
        (Just c1, Nothing) -> Just $ mkMiddle $ con c1 s2
        (Nothing, Just c2) -> Just $ mkMiddle $ con s1 c2
        (Just c1, Just c2) -> Just $ mkMiddle $ con c1 c2
    rewrite1 f con s =
      case lp f s of
        Nothing -> Nothing
        Just c1 -> Just $ mkMiddle $ con c1
    rewriteLast f con s =
      case lp f s of
        Nothing -> Nothing
        Just c1 -> Just $ mkLast $ con c1

simplify :: FuelMonad m => FwdRewrite m (Quad Operand) f
simplify = mkFRewrite rw where
  rw :: FuelMonad m => (Quad Operand) e x -> f -> m (Maybe(Graph (Quad Operand) e x))
  rw q _ = return $ case q of
    QCompOp d op (LitInt i1) (LitInt i2) ->
      let {fn = case op of
        L -> (<)
        LE -> (<=)
        G -> (>)
        GE -> (>=)
        E -> (==)
        NE -> (/=) }
      in simpl d $ toInt $ fn i1 i2
    QBinOp d QDiv _ (LitInt 0) -> Nothing
    QBinOp d QMod _ (LitInt 0) -> Nothing
    QBinOp d op (LitInt i1) (LitInt i2) ->
      let {fn = case op of
        QAdd -> (+)
        QSub -> (-)
        QMul -> (*)
        QDiv -> div
        QMod -> mod}
      in simpl d $ fn i1 i2
    QAnd d (LitInt i1) (LitInt i2) ->
      simpl d $ toInt $ toBool i1 && toBool i2
    QOr d (LitInt i1) (LitInt i2) ->
      simpl d $ toInt $ toBool i1 || toBool i2
    QNeg d (LitInt i) ->
      simpl d $ -i
    QNot d (LitInt i) ->
      simpl d $ toInt $ not $ toBool i
    QGotoBool (LitInt 0) _ l2 ->
      Just $ mkLast $ QGoto l2
    QGotoBool (LitInt _) l1 _ ->
      Just $ mkLast $ QGoto l1
    _ -> Nothing
    where
      simpl d i = Just $ mkMiddle $ QCopy d $ LitInt i
      toInt b = if b then toInteger 1 else toInteger 0
      toBool i = i /= 0

propPass :: FuelMonad m => FwdPass m (Quad Operand) PropFact
propPass = FwdPass {
  fp_lattice = propLattice,
  fp_transfer = varIsLit,
  fp_rewrite = propRewrite `thenFwdRw` simplify
}

propOptFun :: QFunDef -> QFunDef
propOptFun (QFunDef ident type_ (l, graph) params) =
  QFunDef ident type_ (l, newgraph) params
  where
    (newgraph, _, _) = runSimpleUniqueMonad $
      (runWithFuel :: Monad m => Fuel -> InfiniteFuelMonad m a -> m a) infiniteFuel $
        analyzeAndRewriteFwd propPass (JustC [l]) graph facts
    facts = mapSingleton l $ initFact [Reg $ "~p" ++ show i | i <- [0..params-1]]

type LiveVars = Set.Set Operand

liveLattice :: DataflowLattice LiveVars
liveLattice = DataflowLattice {
  fact_name = "live registers" ,
  fact_bot = Set.empty,
  fact_join = join
} where
  join _ (OldFact old) (NewFact new) = (ch, j)
    where
      j = Set.union new old
      ch = changeIf (Set.size j > Set.size old)

liveTransfer :: BwdTransfer (Quad Operand) LiveVars
liveTransfer = mkBTransfer tr
  where
    tr :: (Quad Operand) e x -> Fact x LiveVars -> LiveVars
    tr q f = case q of
      QLabel _  -> f
      QCopy d s -> addUse s $ delUse d f
      QBinOp d op s1 s2 -> update2 d s1 s2 f
      QCompOp d op s1 s2 -> update2 d s1 s2 f
      QAnd d s1 s2 -> update2 d s1 s2 f
      QOr d s1 s2 -> update2 d s1 s2 f
      QNeg d s -> update1 d s f
      QNot d s -> update1 d s f
      QLoad d s -> update1 d s f
      QStore d s -> addUse d $ addUse s f
      QGoto l -> factL f l
      QGotoBool r l1 l2 -> addUse r $ factL f l1 `Set.union` factL f l2
      QParam r -> addUse r f
      QCall _ _ -> f
      QCallExternal _ _ -> f
      QVRet -> fact_bot liveLattice
      QRet r -> addUse r $ fact_bot liveLattice
      QAlloca d -> delUse d f
      QError -> fact_bot liveLattice
    delUse = Set.delete
    addUse o f =
      case o of
        LitInt _ -> f
        _ -> Set.insert o f
    update2 d s1 s2 f = addUse s1 $ addUse s2 $ delUse d f
    update1 d s f = addUse s $ delUse d f
    factL factbase l = fromMaybe Set.empty $ lookupFact l factbase

deadElimRewrite :: FuelMonad m => BwdRewrite m (Quad Operand) LiveVars
deadElimRewrite = mkBRewrite elim
  where
    elim :: Monad m => (Quad Operand) e x -> Fact x LiveVars -> m (Maybe (Graph (Quad Operand) e x))
    elim q f = return $ case q of
      QCopy d _ -> elimIf d f
      QBinOp d _ _ _ -> elimIf d f
      QCompOp d _ _ _ -> elimIf d f
      QAnd d _ _ -> elimIf d f
      QOr d _ _ -> elimIf d f
      QNeg d _ -> elimIf d f
      QNot d _ -> elimIf d f
      QLoad d _ -> elimIf d f
      QAlloca d -> elimIf d f
      _ -> Nothing
    elimIf d f = if not (Set.member d f) then Just emptyGraph else Nothing

deadElimPass = BwdPass {
  bp_lattice = liveLattice,
  bp_transfer = liveTransfer,
  bp_rewrite = deadElimRewrite
}

deadElimOptFun :: QFunDef -> QFunDef
deadElimOptFun (QFunDef ident type_ (l, graph) params) =
  QFunDef ident type_ (l, newgraph) params
  where
    (newgraph, _, _) = runSimpleUniqueMonad $
      (runWithFuel :: Monad m => Fuel -> InfiniteFuelMonad m a -> m a) infiniteFuel $
        analyzeAndRewriteBwd deadElimPass (JustC [l]) graph mapEmpty
