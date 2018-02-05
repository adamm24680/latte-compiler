{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GenAsm (genNasmRepr)
  where

import           Compiler.Hoopl             (C, Graph, Label)
import           Control.Monad.State.Strict
import           Data.List                  (intercalate)
import qualified Data.Map                   as Map
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set                   as Set

import           IR
import           Linearize
import           Linearscan
import           Liveness                   (LiveAnnotated)
import           X86DSL



data GenSt = GenSt {
  instrs      :: [X86Ins] ,
  funMapping  :: Map.Map Ident X86Label,
  counter     :: Int,
  externs     :: Set.Set String,
  stackOffset :: Int,
  params      :: [X86Op],
  vtables     :: (Map.Map Ident X86Label, [QVTable])
}

type GenM a = State GenSt a


instance Show (PhysOp X86Reg) where
  show (PhysReg r)    = show r
  show (Constant i)   = show i
  show (StackSlot i)  = "[" ++ show Ebp ++ "-"++ show (4*(i+1))++"]"
  show (StackParam i) = "[" ++ show Ebp ++ "+"++ show (4*(i+2))++"]"
  show NoReg          = "__noreg__"


emit :: X86Ins -> GenM ()
emit ins =
  modify $ \s -> s{instrs = elimNoReg ins : instrs s}

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
  PhysReg reg  -> PReg reg
  Constant i   -> PImm $ fromInteger i
  StackSlot i  -> PEAddress $ AOff ebp (-4 * (i+1))
  StackParam i -> PEAddress $ AOff ebp (4 * (i+2))
  NoReg        -> NoX86Reg

toX86Label :: Label -> X86Label
toX86Label l = X86Label $ "." ++ show l

exitLabel :: X86Label
exitLabel = X86Label ".exit"

genQ :: Ins X86Op -> GenM ()
genQ (Fst q) = case q of
  QLabel l -> emit $ Label $ toX86Label l
genQ (Mid q) = case q of
  QBinOp d op s1 s2 -> do
    emit $ Mov eax s1
    case op of
      QAdd ->
        emit $ Add eax s2
      QSub ->
        emit $ Sub eax s2
      QMul -> do
        emit $ Push edx
        case s2 of -- cannot multiply by immediate
          PImm _ -> do
            emit $ Push s2
            emit $ Imul $ PEAddress $ AReg esp
            emit $ Add esp $ PImm 4
          _ -> emit $ Imul s2
        emit $ Pop edx
      QDiv -> do
        emit $ Push edx
        emit $ Mov edx $ PImm 0
        case s2 of -- cannot divide by immediate
          PImm _ -> do
            emit $ Push s2
            emit $ Idiv $ PEAddress $ AReg esp
            emit $ Add esp $ PImm 4
          _ -> emit $ Idiv s2
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
      L  -> CL
      LE -> CLE
      G  -> CG
      GE -> CGE
      E  -> CZ
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
    emit $ Sub eax $ PImm 1
    emit $ Neg eax
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
    let errorS = "internal error - function not found"
    fnLabel <- (fromMaybe (error errorS) . Map.lookup ident . funMapping) <$> get
    emitFun d $ PLabel fnLabel
  QCallExternal d lbl -> do
    modify $ \st -> st{externs = Set.insert lbl $ externs st}
    emitFun d $ PLabel $ X86Label lbl
  QCallVirtual d s i -> do
    emit $ Mov eax s
    emit $ Mov eax (PEAddress $ AReg eax)
    emit $ Mov eax (PEAddress $ AOff eax (4 * i))
    emitFun d $ PReg eax
  QLoadVtable d ident -> do
    vtbls <- gets $ fst. vtables
    let vtable = fromMaybe (error "internal error - vtable not found)") $
                  Map.lookup ident vtbls
    emit $ Mov d $ PLabel vtable
  where
    emitFun d lbl = do
      emit $ Push ecx
      emit $ Push edx
      ps <- params <$> get
      forM_ ps $ \op -> emit $ Push op
      modify $ \st -> st{params = []}
      emit $ Call lbl
      emit $ Add esp $ PImm (4 * length ps)
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
    emit $ Jnz $ PLabel $ toX86Label l1
    emit $ Jmp $ PLabel $ toX86Label l2
  QVRet -> emit $ Jmp $ PLabel exitLabel
  QError -> emit $ Call $ PLabel $ X86Label "abort"

genFun :: (QFunDef [Ins (PhysOp X86Reg)], Int) -> GenM ()
genFun (QFunDef ident _ insns _, locals) = do
  let insns2 = map (fmap convOp) insns
  modify $ \s -> s {stackOffset = -4 * locals}
  when (ident == Ident "main") (do
    emit $ Label $ X86Label "main"
    genLoadVTables)
  let errorS = "internal error - function " ++ show ident ++ " not found"
  fnlabel <- (fromMaybe (error errorS) . Map.lookup ident . funMapping) <$> get
  emit $ Label fnlabel

  emit $ Push ebp
  emit $ Mov ebp esp
  emit $ Sub esp $ PImm $ 4 * locals
  emit $ Push ebx
  emit $ Push esi
  emit $ Push edi
  forM_ insns2 genQ
  emit $ Label exitLabel
  emit $ Pop edi
  emit $ Pop esi
  emit $ Pop ebx
  emit $ Add esp $ PImm $ 4 * locals
  emit $ Pop ebp
  emit Ret

  modify $ \s -> s {stackOffset = 0}

genLoadVTables :: GenM ()
genLoadVTables = do
  (mapping, vtables) <- gets vtables
  forM_ vtables $ loadtable mapping
  where
    loadtable mapping (QVTable ident funs) = do
      let table = fromMaybe (error "genLoadVTables") $ Map.lookup ident mapping
      forM_ (zip [0..] funs) $ genLoadVTable table

genLoadVTable :: X86Label -> (Int, Ident) -> GenM ()
genLoadVTable label (index, ident) = do
  mapping <- gets funMapping
  let funLabel = fromMaybe (error "genLoadVTable") $ Map.lookup ident mapping
  emit $ Mov edx $ PLabel label
  emit $ Mov eax $ PLabel funLabel
  emit $ Mov (PEAddress $ AOff edx $ 4 * index) eax

genVTables :: [QVTable] -> Map.Map Ident X86Label -> [String]
genVTables list mapping =
  "section .bss" : tables
  where
    tables = concatMap genVTable list
    extractLabel = fromMaybe (error "vtable for ident not found")
    genVTable (QVTable ident funs) =
      [show (extractLabel $ Map.lookup ident mapping) ++ ":",
        "    resd " ++ show (length funs)]

genNasmRepr :: [QFunDef (Label, Graph LiveAnnotated C C)] -> [QVTable]-> [String]
genNasmRepr funlist vtables = [sectdecl, globdecl, extdecl] ++ inslist ++ vtabledecl
  where
    mapping = Map.fromList $
      zip (map (\(QFunDef ident _ _ _) -> ident) funlist) $
        map (\i -> X86Label $ "F"++ show i) [1..length funlist]
    vtablemapping = Map.fromList $
      zip (map (\(QVTable ident l) -> ident) vtables) $
        map (\i -> X86Label $ "VT"++ show i) [1..length funlist]
    allocated = map linearizeAndAlloc funlist
    gen = forM_ allocated genFun
    res = execState gen GenSt{instrs = [], funMapping = mapping, counter = 0,
                              externs = Set.empty, stackOffset = 0, params = [],
                              vtables = (vtablemapping, vtables)}
    extrs = Set.insert "abort" $ externs res
    extdecl = "    extern "++ intercalate "," (Set.toList extrs)
    globdecl = "    global main"
    sectdecl = "section .text"
    generated = reverse $ instrs res
    rewrites1 = [elimNop, elimMov, elimAdd0]
    rewrites2 = [elimMov2, jmpElim]
    rewrites3 = []
    optimized = peepholeOpt rewrites1 rewrites2 rewrites3 generated []
    inslist = map show optimized
    vtabledecl = genVTables vtables vtablemapping


type Rewrite1 = X86Ins -> Maybe [X86Ins]
type Rewrite2 = (X86Ins, X86Ins) -> Maybe [X86Ins]
type Rewrite3 = (X86Ins, X86Ins, X86Ins) -> Maybe [X86Ins]

peepholeOpt :: [Rewrite1] -> [Rewrite2] -> [Rewrite3] ->
  [X86Ins] -> [X86Ins] -> [X86Ins]
peepholeOpt r1 r2 r3 insns acc = case insns of
  [] -> reverse acc
  (h:t) -> case applyUntil (rewrites1 ++ rewrites2 ++ rewrites3) insns of
    Just res -> peepholeOpt r1 r2 r3 res acc
    Nothing  -> peepholeOpt r1 r2 r3 t (h:acc)
  where
    apply1 r l = case l of
      h1:t -> fmap (++ t) (r h1)
      _    -> Nothing
    apply2 r l = case l of
      h1:h2:t -> fmap (++ t) (r (h1, h2))
      _       -> Nothing
    apply3 r l = case l of
      h1:h2:h3:t -> fmap (++ t) (r (h1, h2, h3))
      _          -> Nothing
    rewrites1 = map apply1 r1
    rewrites2 = map apply2 r2
    rewrites3 = map apply3 r3
    applyUntil :: [[X86Ins] ->
      Maybe [X86Ins]] -> [X86Ins] -> Maybe [X86Ins]
    applyUntil [] l = Nothing
    applyUntil (r:t) l = case r l of
      Just l2 -> Just l2
      Nothing -> applyUntil t l

elimNop i = case i of
  Nop -> Just []
  _   -> Nothing

elimMov i = case i of
  Mov a b -> if a == b then Just [] else Nothing
  _       -> Nothing

elimMov2 i = case i of
  (Mov a1 b1, Mov a2 b2) ->
    if a1 == b2 && a2 == b1 then
      Just [Mov a1 b1]
    else
      Nothing
  _ -> Nothing

elimAdd0 i = case i of
  Add _ (PImm 0) -> Just []
  Add (PImm 0) _ -> Just []
  Sub _ (PImm 0) -> Just []
  Sub (PImm 0) _ -> Just []
  _              -> Nothing

jmpElim i = case i of
  (Jmp (PLabel l1), Label l2) ->
    if l1 == l2 then Just [Label l2] else Nothing
  _ -> Nothing
