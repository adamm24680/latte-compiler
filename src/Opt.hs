{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
--module Opt (propOptFun, deadElimOptFun)
module Opt (propOptFun)
  where

import           AbsLatte       (Ident)
import           Compiler.Hoopl
import qualified Data.Map       as Map
import           Data.Maybe
import qualified Data.Set       as Set
import           IR             (BinOp (..), CompOp (..), Operand (..),
                                 QFunDef (..), Quad (..))


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
      --QAlloca d -> Map.insert d CTop f
      QError -> mapEmpty
      --QLoadParam d i -> Map.insert d CTop f

propRewrite :: FuelMonad m => FwdRewrite m (Quad Operand) PropFact
propRewrite = mkFRewrite rw
  where
    rw :: FuelMonad m => (Quad Operand) e x -> PropFact -> m (Maybe(Graph (Quad Operand) e x))
    rw q f = return $ case q of
      QBinOp d op s1 s2  -> rewrite2 f (QBinOp d op) s1 s2
      QCompOp d op s1 s2 -> rewrite2 f (QCompOp d op) s1 s2
      QAnd d s1 s2       -> rewrite2 f (QAnd d) s1 s2
      QOr d s1 s2        -> rewrite2 f (QOr d) s1 s2
      QNeg d s           -> rewrite1 f (QNeg d) s
      QNot d s           -> rewrite1 f (QNot d) s
      QLoad d s          -> rewrite1 f (QLoad d) s
      QStore d s         -> rewrite1 f (QStore d) s
      QCopy d s          -> rewrite1 f (QCopy d) s
      QGotoBool r l1 l2  -> rewriteLast f (\r1 -> QGotoBool r1 l1 l2) r
      QParam r           -> rewrite1 f QParam r
      --QPhi d s1 s2 -> rewrite2 f (QPhi d) s1 s2
      QRet r             -> rewriteLast f QRet r
      _                  -> Nothing
    lp f v = case Map.lookup v f of
      Just (Copied(LitInt i)) -> Just (LitInt i)
      --Just (Copied o) -> Just o
      _                       -> Nothing
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
        L  -> (<)
        LE -> (<=)
        G  -> (>)
        GE -> (>=)
        E  -> (==)
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

propOptFun :: QFunDef (Label, Graph (Quad Operand) C C) -> QFunDef (Label, Graph (Quad Operand) C C)
propOptFun (QFunDef ident type_ (l, graph) params) =
  QFunDef ident type_ (l, newgraph) params
  where
    (newgraph, _, _) = runSimpleUniqueMonad $
      (runWithFuel :: Monad m => Fuel -> InfiniteFuelMonad m a -> m a) infiniteFuel $
        analyzeAndRewriteFwd propPass (JustC [l]) graph facts
    facts = mapSingleton l Map.empty
