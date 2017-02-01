{-# LANGUAGE FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module RegAlloc where

import IR
import Compiler.Hoopl (Graph, foldGraphNodes, C, O)
import LinearScan.Hoopl
import LinearScan (PhysReg(..), VarId(..), VarKind(..), VarInfo(..))
import qualified Data.Bimap as B

nreg = 5 -- ebx, ecx, edx, edi, esi

data AllocatedOp = Register PhysReg | StackSlot Int | Constant Integer

instance NodeAlloc (Quad Operand) (Quad AllocatedOp) where
  isCall (QCall _ _) = True
  isCall (QCallExternal _ _) = True
  isCall _ = False

  isBranch (QGoto _) = True
  isBranch QGotoBool{} = True
  isBranch _ = False

  retargetBranch (QGoto l1) tl1 tl2 =
    if l1 == tl1 then QGoto tl2 else QGoto l1
  retargetBranch (QGotoBool r l1 l2) tl1 tl2
    | l1 == tl1 = QGotoBool r tl2 l2
    | l2 == tl2 = QGotoBool r l1 tl2
    | otherwise = QGotoBool r l1 l2
  retargetBranch b _ _ = b

  mkLabelOp = QLabel
  mkJumpOp = QGoto

  getReferences = undefined
  setRegisters = undefined
  mkMoveOps  = undefined
  mkSaveOps = undefined
  mkRestoreOps = undefined
  op1ToString = show

buildVarMap :: Graph (Quad Operand) C C -> B.Bimap Operand VarId
buildVarMap g = B.fromList $ fst $ foldGraphNodes accFun g ([], 0)
  where
    ins (LitInt _) m = m
    ins d (mappings, counter) = ((d, counter):mappings, counter+1)
    accFun :: Num t => Quad Operand e x -> ([(Operand, t)], t) -> ([(Operand, t)], t)
    accFun q acc = case q of
      QBinOp d _ _ _ -> ins d acc
      QCompOp d _ _ _ -> ins d acc
      QAnd d _ _ -> ins d acc
      QOr d _ _ -> ins d acc
      QNeg d _ -> ins d acc
      QNot d _ -> ins d acc
      QLoad d _ -> ins d acc
      QCopy d _ -> ins d acc
      QCall d _ -> ins d acc
      QCallExternal d _ -> ins d acc
      QAlloca d -> ins d acc
      QLoadParam d _ -> ins d acc
      _ -> acc
