{-# LANGUAGE FlexibleInstances, GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GenAsm (genNasmRepr)
  where

import Compiler.Hoopl (Graph, C, Label)
import Control.Monad.State.Strict
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Data.List (intercalate)

import Linearscan
import Linearize
import IR
import Liveness (LiveAnnotated)
import X86DSL



data GenSt = GenSt {
  instrs :: [X86Ins] ,
  funMapping :: Map.Map Ident X86Label,
  counter :: Int,
  externs :: Set.Set String,
  stackOffset :: Int,
  params :: [X86Op]
}

type GenM a = State GenSt a


instance Show (PhysOp X86Reg) where
  show (PhysReg r) = show r
  show (Constant i) = show i
  show (StackSlot i) = "[" ++ show Ebp ++ "-"++ show (4*(i+1))++"]"


emit :: X86Ins -> GenM ()
emit ins =
  modify $ \s -> s{instrs = ins : instrs s}

newLabel :: GenM X86Label
newLabel = do
  num <- counter <$> get
  modify $ \s -> s{counter = num + 1}
  return $ X86Label $ ".tl_"++ show num

linearizeAndAlloc :: QFunDef (Label, Graph LiveAnnotated C C) ->
  (QFunDef [Ins (PhysOp X86Reg)], Int)
linearizeAndAlloc (QFunDef ident type_ g parms) =
  (QFunDef ident type_ g2 parms, i)
  where (g2, i) = linearScan [Ebx, Ecx, Edx, Edi, Esi] $ linearizeAnnotated g

convOp :: PhysOp X86Reg -> X86Op
convOp pr = case pr of
  PhysReg reg -> PReg reg
  Constant i -> PImm $ fromInteger i
  StackSlot i -> PEAddress $ AOff ebp i

toX86Label :: Label -> X86Label
toX86Label l = X86Label $ "." ++ show l

exitLabel :: X86Label
exitLabel = X86Label ".exit"

genQ :: Ins X86Op -> GenM ()
genQ (Fst q) = case q of
  QLabel l -> emit $ Label $ toX86Label l
genQ (Mid q) = case q of
  QAlloca d -> do
    modify $ \s -> s{stackOffset = stackOffset s - 4}
    off <- stackOffset <$> get
    emit $ Mov d ebp
    emit $ Add d $ PImm off
  QBinOp d op s1 s2 -> do
    emit $ Mov eax s1
    case op of
      QAdd ->
        emit $ Add eax s2
      QSub ->
        emit $ Sub eax s2
      QMul -> do
        emit $ Push edx
        emit $ Imul s2
        emit $ Pop edx
      QDiv -> do
        emit $ Push edx
        emit $ Mov edx $ PImm 0
        emit $ Idiv s2
        emit $ Pop edx
      QMod -> do
        emit $ Push edx
        emit $ Mov edx $ PImm 0
        emit $ Idiv s2
        emit $ Mov eax edx
        emit $ Pop edx
    emit $ Mov d eax
  QCompOp d op s1 s2 -> do
    emit $ Mov eax s1
    emit $ Cmp eax s2
    emit $ Mov eax $ PImm 0
    let {cond = case op of
      L -> CL
      LE -> CLE
      G -> CG
      GE -> CGE
      E -> CZ
      NE -> CNZ }
    emit $ Setcc cond
    emit $ Mov d eax
  QAnd d s1 s2 -> do
    emit $ Mov eax s1
    emit $ And eax s2
    emit $ Mov d eax
  QOr d s1 s2 -> do
    emit $ Mov eax s1
    emit $ Or eax s2
    emit $ Mov d eax
  QNeg d s -> do
    emit $ Mov eax s
    emit $ Neg eax
    emit $ Mov d eax
  QNot d s -> do
    emit $ Mov eax s
    emit $ Not eax
    emit $ Mov d eax
  QLoad d s -> do
    emit $ Mov eax s
    emit $ Mov eax $ PEAddress $ AReg eax
    emit $ Mov d eax
  QStore d s -> do
    emit $ Mov eax d
    case s of
      PEAddress _ -> do
        emit $ Push edx
        emit $ Mov edx s
        emit $ Mov (PEAddress $ AReg eax) edx
        emit $ Pop edx
      _ -> emit $ Mov (PEAddress $ AReg eax) s
  QCopy d s ->
    case (d,s) of
      (PEAddress _, PEAddress _) -> do
        emit $ Mov eax s
        emit $ Mov d eax
      _ -> emit $ Mov d s
  QParam s ->
    modify $ \st -> st {params = s : params st}
  QCall d ident -> do
    fnLabel <- (fromJust. Map.lookup ident . funMapping) <$> get
    emitFun d fnLabel
  QCallExternal d lbl -> do
    modify $ \st -> st{externs = Set.insert lbl $ externs st}
    emitFun d $ X86Label lbl
  QLoadParam d i -> do
    let addr = AOff ebp $ (i+2) *4
    emit $ Mov eax $ PEAddress addr
    emit $ Mov d eax
  where
    emitFun d lbl = do
      emit $ Push ecx
      emit $ Push edx
      ps <- params <$> get
      forM_ ps $ \op -> emit $ Push op
      modify $ \st -> st{params = []}
      emit $ Call $ PLabel lbl
      emit $ Add esp $ PImm (4* length ps)
      emit $ Pop edx
      emit $ Pop ecx
      emit $ Mov d eax
genQ (Lst q) = case q of
  QGoto l -> emit $ Jmp $ PLabel $ toX86Label l
  QRet s -> do
    emit $ Mov eax s
    emit $ Jmp $ PLabel exitLabel
  QGotoBool r l1 l2 -> do
    emit $ Cmp r $ PImm 0
    emit $ Jz $ PLabel $ toX86Label l1
    emit $ Jmp $ PLabel $ toX86Label l2
  QVRet -> emit $ Jmp $ PLabel exitLabel
  QError -> emit $ Call $ PLabel $ X86Label "abort"

genFun :: (QFunDef [Ins (PhysOp X86Reg)], Int) -> GenM ()
genFun (QFunDef ident type_ insns parms, locals) = do
  let allocas = length $ filter id $
                  map (\ins -> case ins of
                                Mid (QAlloca _) -> True
                                _ -> False)
                  insns
  let insns2 = map (fmap convOp) insns
  modify $ \s -> s {stackOffset = -4 * locals}
  when (ident == Ident "main") $ emit $ Label $ X86Label "main"
  fnlabel <- (fromJust . Map.lookup ident . funMapping) <$> get
  emit $ Label fnlabel

  emit $ Push ebp
  emit $ Mov ebp esp
  emit $ Sub esp $ PImm $ 4 * (allocas + locals)
  emit $ Push ebx
  emit $ Push esi
  emit $ Push edi
  forM_ insns2 genQ
  emit $ Label exitLabel
  emit $ Pop edi
  emit $ Pop esi
  emit $ Pop ebx
  emit $ Add esp $ PImm $ 4 * (allocas + locals)
  emit $ Pop ebp
  emit Ret

  modify $ \s -> s {stackOffset = 0}

genNasmRepr :: [QFunDef (Label, Graph LiveAnnotated C C)] -> [String]
genNasmRepr funlist = [sectdecl, globdecl, extdecl] ++ reverse inslist
  where
    mapping = Map.fromList $
      zip (map (\(QFunDef ident _ _ _) -> ident) funlist) $
        map (\i -> X86Label $ "F"++ show i) [1..length funlist]
    allocated = map linearizeAndAlloc funlist
    gen = forM_ allocated genFun
    res = execState gen GenSt{instrs=[], funMapping = mapping, counter=0,
                              externs = Set.empty, stackOffset=0, params = []}
    extrs = Set.insert "abort" $ externs res
    extdecl = "    extern "++ intercalate "," (Set.toList extrs)
    globdecl = "    global main"
    sectdecl = "section .text"
    inslist = map show $ instrs res