{-# LANGUAGE FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module RegAlloc (AllocatedOp(..), allocateRegisters)
 where

import IR
import Compiler.Hoopl (Graph, foldGraphNodes, C, O, mapGraph)
import LinearScan.Hoopl
import LinearScan (PhysReg(..), VarId(..), VarKind(..), VarInfo(..), UseVerifier(..))
import LinearScan.Hoopl.DSL (getStackSlot)
import qualified Data.Bimap as B
import Text.Printf
import Data.List
import Data.Maybe

nreg = 5 -- ebx, ecx, edx, edi, esi

data AllocatedOp = Register PhysReg | StackSlot Int | Constant Integer
data PreAllocRegs = Var VarInfo | Const Integer

instance PrintfArg PreAllocRegs where
  formatArg (Var varinfo) _ = showString $ "v" ++ show (varId varinfo)
  formatArg (Const i) _ = shows i

instance PrintfArg AllocatedOp where
  formatArg (Register r) _ = case r of
    0 -> showString "ebx"
    1 -> showString "ecx"
    2 -> showString "edx"
    3 -> showString "esi"
    4 -> showString "edi"
    _ -> showString "__!noreg__"
  formatArg (StackSlot i) _ = showString $ "[ebp-" ++ show (i +4) ++ "]"
  formatArg (Constant i) _ = shows i

instance Eq VarInfo where
  (==) a b =
    varId a == varId b && varKind a == varKind b && regRequired a == regRequired b

instance NodeAlloc (Quad PreAllocRegs) (Quad AllocatedOp) where
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

  getReferences q = clean $ concatMap getVarInfo rt
    where
      rt :: [PreAllocRegs]
      rt = case q of
        QBinOp d op s1 s2 -> [d, s1, s2]
        QCompOp d op s1 s2 -> [d, s1, s2]
        QAnd d s1 s2 -> [d, s1, s2]
        QOr d s1 s2 -> [d, s1, s2]
        QNeg d s -> [d,s]
        QNot d s -> [d,s]
        QLoad d s -> [d,s]
        QStore s1 s2 -> [s1, s2]
        QCopy d s -> [d,s]
        QGoto _ -> []
        QGotoBool r _ _ -> [r]
        QParam r -> [r]
        QCall d _ -> [d]
        QCallExternal d _ -> [d]
        QLabel _ -> []
        QVRet -> []
        QRet r -> [r]
        QAlloca d -> [d]
        QError -> []
        QLoadParam d _ -> [d]
      getVarInfo (Const i) = []
      getVarInfo (Var vi) = [vi]
      clInOut v =
        VarInfo {varId = v, varKind = InputOutput, regRequired = True}
      clean l =
        fromMaybe l cl
        where {cl = do
          a <- find (\a -> varKind a == Output) l
          b <- find (\b -> varKind b == Input && varId b == varId a) l
          return $ clInOut (varId a) : filter (\c -> varId c /= varId a) l}

  setRegisters l q = return $ qmap apply q
    where
      apply (Const i) = Constant i
      apply (Var varinfo) =
        let (Right v) = varId varinfo in
        case lookup (v, varKind varinfo) l of
          Just reg -> Register reg
          Nothing -> Register (-1)
  mkMoveOps sreg _ dreg =
    return [QCopy (Register dreg) (Register sreg)]
  mkSaveOps sreg dvar = do
    off <- getStackSlot (Just dvar)
    return [QStore (StackSlot off) (Register sreg)]
  mkRestoreOps dreg svar = do
    off <- getStackSlot (Just svar)
    return [QLoad (Register dreg) (StackSlot off)]
  op1ToString = show


convNode :: B.Bimap Operand VarId -> Quad Operand e x -> Quad PreAllocRegs e x
convNode varmap q = case q of
  QBinOp d op s1 s2 -> QBinOp (mkOut d) op (mkIn s1 ) (mkIn s2)
  QCompOp d op s1 s2 -> QCompOp (mkOut d) op (mkIn s1) (mkIn s2)
  QAnd d s1 s2 -> QAnd (mkOut d)(mkIn s1) (mkIn s2)
  QOr d s1 s2 -> QOr (mkOut d) (mkIn s1) (mkIn s2)
  QNeg d s -> QNeg (mkOut d) (mkIn s)
  QNot d s -> QNot (mkOut d) (mkIn s)
  QLoad d s -> QLoad (mkOut d) (mkIn s)
  QStore s1 s2 -> QStore (mkIn s1) (mkIn s2)
  QCopy d s -> QCopy (mkOut d) (mkIn s)
  QGoto l -> QGoto l
  QGotoBool r l1 l2 -> QGotoBool (mkIn r) l1 l2
  QParam r -> QParam $ mkIn r
  QCall d l -> QCall (mkOut d) l
  QCallExternal d l -> QCallExternal (mkOut d) l
  QLabel l -> QLabel l
  QVRet -> QVRet
  QRet r -> QRet (mkIn r)
  QAlloca d -> QAlloca (mkOut d)
  QError -> QError
  QLoadParam d i -> QLoadParam (mkOut d) i
  where
    mkVarInfo kind v =
      case v of
        LitInt i -> Const i
        Reg _ -> case B.lookup v varmap of
          Just varid -> Var VarInfo {varId = Right varid,
                          varKind = kind, regRequired = True}
          Nothing -> error "error in regalloc (undefined variable used)"
    mkIn = mkVarInfo Input
    mkOut = mkVarInfo Output

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


allocateRegisters :: QFunDef Operand -> QFunDef AllocatedOp
allocateRegisters (QFunDef ident type_ (l, graph) params) =
  QFunDef ident type_ (l, rg) params
  where
    varMap = buildVarMap graph
    mapped = mapGraph (convNode varMap) graph
    (d, res) = allocateHoopl nreg 0 4 VerifyDisabled l mapped
    rg = case res of
      Left l -> error $ "error during regalloc:\n" ++ unlines l
      Right r -> r
