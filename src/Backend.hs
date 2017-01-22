module Backend where


import qualified Data.Map as Map
import AbsLatte
import Control.Monad
import Control.Monad.RWS

data Operand = Reg String | LitInt Integer | LitBool Bool
newtype Label = Label String

data BinOp = QAdd | QSub | QMul | QDiv | QMod
data CompOp = L | LE | G | GE | E | NE

data Quadruple =
  QBinOp Operand BinOp Operand Operand |
  QCompOp Operand CompOp Operand Operand |
  QAnd Operand Operand Operand |
  QOr Operand Operand Operand |
  QNeg Operand Operand |
  QNot Operand Operand |
  QLoad Operand Operand |
  QStore Operand Operand |
  QCopy Operand Operand |
  QGoto Label |
  QGotoComp Operand CompOp Operand Label Label |
  QGotoBool Operand Label Label |
  QParam Operand |
  QCall Operand Label |
  QLabel Label |
  QPhi Operand Operand Operand

type GenM a = RWS () [Quadruple] () a

emit :: Quadruple -> GenM ()
emit a = tell [a]

emitBin :: (Operand -> a -> Operand -> Operand -> Quadruple) -> a ->
  Operand -> Operand -> GenM Operand
emitBin con op r1 r2 = do
  dest <- newReg
  tell [con dest op r1 r2]
  return dest

emitAnd r1 r2 = do
  dest <- newReg
  tell [QAnd dest r1 r2]
  return dest

emitOr r1 r2 = do
  dest <- newReg
  tell [QOr dest r1 r2]
  return dest

emitPhi r1 r2 = do
  dest <- newReg
  tell [QPhi dest r1 r2]
  return dest

emitUn :: (Operand -> Operand -> Quadruple) -> Operand -> GenM Operand
emitUn con r = do
  dest <- newReg
  tell [con dest r]
  return dest

emitParam :: Operand -> GenM ()
emitParam operand = tell [QParam operand]

emitCall :: Label -> GenM Operand
emitCall label = do
  dest <- newReg
  tell [QCall dest label]
  return dest

emitWrite :: Operand -> Int -> Operand -> GenM ()
emitWrite base offset value = do
  dest <- emitBin QBinOp QAdd (LitInt . toInteger $(4*offset)) base
  emit $ QStore dest value


newReg :: GenM Operand
newReg = undefined

newLabel :: GenM Label
newLabel = undefined

getFunLabel :: Ident -> GenM Label
getFunLabel ident = undefined

getAddr :: Ident -> GenM Operand
getAddr = undefined

genExpr :: Expr -> GenM Operand
genExpr x = case x of
  EVar ident -> do
    a <- getAddr ident
    emitUn QLoad a
  ELitInt integer -> return $ LitInt integer
  ELitTrue -> return $ LitBool True
  ELitFalse -> return $ LitBool False
  EApp ident exprs -> do
    vs <- mapM genExpr exprs
    mapM_ emitParam vs
    label <- getFunLabel ident
    emitCall label
  EString string -> do
    let label = Label "calloc" -- TODO
    emitParam $ LitInt . toInteger $ (length string + 1)
    emitParam $ LitInt 4
    allocated <- emitCall label
    let writes = [emitWrite allocated (offset-1) value | (offset, value) <- zip [1..(length string)] (map (LitInt . toInteger. fromEnum) string)]
    sequence_ writes
    return allocated
  Neg expr -> do
    e <- genExpr expr
    emitUn QNeg e
  Not expr -> do
    e <- genExpr expr
    emitUn QNot e
  EMul expr1 mulop expr2 ->
    let {op = case mulop of
      Times -> QMul
      Div -> QDiv
      Mod -> QMod}
    in do
      e1 <- genExpr expr1
      e2 <- genExpr expr2
      emitBin QBinOp op e1 e2
  EAdd expr1 addop expr2 ->
    let {op = case addop of
      Plus -> QAdd
      Minus -> QSub}
    in do
      e1 <- genExpr expr1
      e2 <- genExpr expr2
      emitBin QBinOp op e1 e2
  ERel expr1 relop expr2 ->
    let {op = case relop of
      LTH -> L
      AbsLatte.LE -> Backend.LE
      GTH -> G
      AbsLatte.GE -> Backend.GE
      EQU -> E
      AbsLatte.NE -> Backend.NE}
    in do
      e1 <- genExpr expr1
      e2 <- genExpr expr2
      emitBin QCompOp op e1 e2
  EAnd expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 newLabel
    emit $ QGotoBool e1 l1 l2
    emit $ QLabel l1
    e2 <- genExpr expr2
    e3 <- emitAnd e1 e2
    emit $ QGoto l2
    emit $ QLabel l2
    emitPhi e1 e2
  EOr expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 newLabel
    emit $ QGotoBool e1 l2 l1
    emit $ QLabel l1
    e2 <- genExpr expr2
    e3 <- emitAnd e1 e2
    emit $ QGoto l2
    emit $ QLabel l2
    emitPhi e1 e2
