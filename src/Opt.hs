{-# LANGUAGE GADTs, ScopedTypeVariables #-}
module Opt (constPropOptFun)
  where

import AbsLatte (Ident)
import IR ( Quad(..), Operand(..), BinOp(..), CompOp(..), QFunDef(..))
import Compiler.Hoopl
import Data.Maybe
import qualified Data.Map as Map


data Const = Const Integer | CTop deriving (Eq)
type ConstFact = Map.Map Operand Const

constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice {
  fact_name = "const var",
  fact_bot = Map.empty,
  fact_join = joinMaps constFactAdd
}
  where
    constFactAdd _ (OldFact old) (NewFact new) =
      case (old, new) of
        (CTop, _) -> (NoChange, CTop)
        (_, CTop) -> (SomeChange, CTop)
        (Const old, Const new) | new == old -> (NoChange, Const new)
                               | otherwise -> (SomeChange, CTop)

initFact :: [Operand] -> ConstFact
initFact ops = Map.fromList  [(v, CTop) | v <- ops]

varIsLit :: FwdTransfer Quad ConstFact
varIsLit = mkFTransfer ft
  where
    ft :: Quad e x -> ConstFact -> Fact x ConstFact
    ft q f = case q of
      QBinOp d op s1 s2 -> Map.insert d CTop f
      QCompOp d op s1 s2 -> Map.insert d CTop f
      QAnd d s1 s2 -> Map.insert d CTop f
      QOr d s1 s2 -> Map.insert d CTop f
      QNeg d s -> Map.insert d CTop f
      QNot d s -> Map.insert d CTop f
      QLoad d s -> Map.insert d CTop f
      QStore d s -> f
      QCopy d (LitInt k) -> Map.insert d (Const k) f
      QCopy d s -> Map.insert d CTop f
      QGoto l -> mapSingleton l f
      QGotoBool r l1 l2 -> mkFactBase constLattice
           [(l1, Map.insert r (Const 1)  f),
            (l2, Map.insert r (Const 0) f)]
      QParam r -> f
      QCall d l -> Map.insert d CTop f
      QCallExternal d l -> Map.insert d CTop f
      --QPhi d s1 s2 -> Map.insert d CTop f
      QVRet -> mapEmpty
      QRet r -> mapEmpty
      QLabel l -> f
      QAlloca d -> Map.insert d CTop f
      QError -> mapEmpty

constProp :: FuelMonad m => FwdRewrite m Quad ConstFact
constProp = mkFRewrite rw
  where
    rw :: FuelMonad m => Quad e x -> ConstFact -> m (Maybe(Graph Quad e x))
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
      Just (Const i) -> Just $ LitInt i
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

simplify :: FuelMonad m => FwdRewrite m Quad f
simplify = mkFRewrite rw where
  rw :: FuelMonad m => Quad e x -> f -> m (Maybe(Graph Quad e x))
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

constPropPass :: FuelMonad m => FwdPass m Quad ConstFact
constPropPass = FwdPass {
  fp_lattice = constLattice,
  fp_transfer = varIsLit,
  fp_rewrite = constProp `thenFwdRw` simplify
}

constPropOptFun :: QFunDef -> QFunDef
constPropOptFun (QFunDef ident type_ (l, graph) params) =
  QFunDef ident type_ (l, newgraph) params
  where
    (newgraph, _, _) = runSimpleUniqueMonad $
      (runWithFuel :: Monad m => Fuel -> InfiniteFuelMonad m a -> m a) infiniteFuel $
        analyzeAndRewriteFwd constPropPass (JustC [l]) graph facts
    facts = mapSingleton l $ initFact [Reg $ "~p" ++ show i | i <- [0..params-1]]
