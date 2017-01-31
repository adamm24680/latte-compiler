{-# LANGUAGE GADTs, ScopedTypeVariables #-}
module Opt where

import AbsLatte (Ident)
import IR ( Quad(..), Operand(..), BinOp(..), CompOp(..))
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
      QPhi d s1 s2 -> Map.insert d CTop f
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
       _ -> Nothing
    lookup f v = case Map.lookup v f of
      Just (Const i) -> Just $ LitInt i
      _ -> Nothing
