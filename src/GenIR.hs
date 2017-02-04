{-# LANGUAGE FlexibleInstances, GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GenIR
  (QFunDef(..), genProgram)
  where

import IR
import qualified Data.Map as Map
import AbsLatte
import Control.Monad
import Control.Monad.RWS
import Text.Printf
import qualified Frontend (predefs)
import Compiler.Hoopl (Label, UniqueMonad, Unique,
 freshUnique, freshLabel, C, O, Graph, (|*><*|),
  mkFirst, mkLast, mkMiddles, emptyClosedGraph, showGraph)
import qualified Compiler.Hoopl as H ((<*>))
import Data.Maybe
import Data.Dynamic


data VarLoc = Stack Operand | Param Int

data GenState = GenState {
  uniqueC :: Unique,
  regCounter:: Integer
  }

data GenEnv = GenEnv {
  varInfo :: Map.Map Ident (VarLoc, Type),
  funInfo :: Map.Map Ident Type}

type GenM = RWS GenEnv [Dynamic] GenState

instance UniqueMonad GenM where
  freshUnique = do
    state <- get
    let number = uniqueC state
    put state{uniqueC = number+1}
    return number

newState :: GenState
newState =
  GenState {uniqueC = 0, regCounter = 0}

newEnv :: GenEnv
newEnv =
  GenEnv { varInfo = Map.empty, funInfo = Map.empty}

insertFunType :: GenEnv -> (Ident, Type) -> GenEnv
insertFunType env (ident, t) =
  env{funInfo = Map.insert ident t $ funInfo env}

getVarLoc :: Ident -> GenM VarLoc
getVarLoc ident = do
  env <- ask
  case Map.lookup ident (varInfo env) of
    Just (loc, _) -> return loc
    Nothing -> fail $ printf "internal error: variable %s not found" ident

getVarType :: Ident -> GenM Type
getVarType ident = do
  env <- ask
  case Map.lookup ident (varInfo env) of
    Just (_, type_) -> return type_
    Nothing -> fail $ printf "internal error: variable %s not found" ident

getFunType :: Ident -> GenM Type
getFunType ident = do
  env <- ask
  case Map.lookup ident $ funInfo env of
    Just x -> return x
    Nothing -> fail $ printf "internal error: function %s not found" ident

insertVar ::  Ident -> VarLoc -> Type -> GenEnv -> GenEnv
insertVar ident varloc type_ env =
  env{varInfo = Map.insert ident (varloc, type_) (varInfo env)}


emit :: (Typeable e, Typeable x) => Quad Operand e x -> GenM ()
emit a = tell [toDyn a]

emitBin :: (Operand -> a -> Operand -> Operand -> Quad Operand O O) -> a ->
  Operand -> Operand -> GenM Operand
emitBin con op r1 r2 = do
  dest <- newReg
  emit $ con dest op r1 r2
  return dest

emitAnd r1 r2 = do
  dest <- newReg
  emit $ QAnd dest r1 r2
  return dest

emitOr r1 r2 = do
  dest <- newReg
  emit $ QOr dest r1 r2
  return dest

--emitPhi r1 r2 = do
--  dest <- newReg
--  emit $ QPhi dest r1 r2
--  return dest

emitUn :: (Operand -> Operand -> Quad Operand O O) -> Operand -> GenM Operand
emitUn con r = do
  dest <- newReg
  emit $ con dest r
  return dest

emitParam :: Operand -> GenM ()
emitParam operand = emit $ QParam operand

emitLoadParam :: Int -> GenM Operand
emitLoadParam i = do
  dest <- newReg
  emit $ QLoadParam dest i
  return dest

emitCall :: Ident -> GenM Operand
emitCall ident = do
  dest <- newReg
  emit $ QCall dest ident
  return dest

emitCallExternal :: String -> GenM Operand
emitCallExternal str = do
  dest <- newReg
  emit $ QCallExternal dest str
  return dest

emitWrite :: Operand -> Int -> Operand -> GenM ()
emitWrite base offset value = do
  dest <- emitBin QBinOp QAdd base (LitInt . toInteger $(4*offset))
  emit $ QStore dest value


emitLoad :: Operand -> GenM Operand
emitLoad reg = do
  new <- newReg
  emit $ QLoad new reg
  return new

emitAlloca :: GenM Operand
emitAlloca = do
  new <- newReg
  emit $ QAlloca new
  return new

emitLabel :: Label -> GenM ()
emitLabel = emit . QLabel

emitStore :: Operand -> Operand -> GenM ()
emitStore dest src = emit $ QStore dest src

newReg :: GenM Operand
newReg = do
  state <- get
  let number = regCounter state
  put state{regCounter = number+1}
  return $ Reg ("r" ++ show number)

--newLabel :: GenM Label
--newLabel = do
  --state <- get
  --let number = labelCounter state
  --put state{labelCounter = number+1}
  --return $ Label ("l" ++ show number)


loadVar :: Ident -> GenM Operand
loadVar ident = do
  loc <- getVarLoc ident
  case loc of
    Stack reg -> return reg
    Param i -> emitLoadParam i

storeVar :: Ident -> Operand -> GenM()
storeVar ident val = do
  loc <- getVarLoc ident
  case loc of
    Stack reg -> emit $ QCopy reg val
    Param _ -> fail "internal error: assignment to parameter"


genDecl :: Type -> Item -> GenM GenEnv
genDecl type_ item = do
  env <- ask
  let {(e, ident) = case item of
    NoInit ident -> (default_ type_, ident)
    Init ident expr -> (expr, ident)}
  uniq <- freshUnique
  let (Ident s) = ident
  let new = Reg $ printf "v%d_%s" uniq s
  let loc = Stack new
  r <- genExpr e
  --emitStore new r
  emit $ QCopy new r
  return $ insertVar ident loc type_ env
  where {default_ t = case t of
    Int -> ELitInt 0
    Bool -> ELitFalse
    Str -> EString ""
    _ -> error "declared variable with function type"}

inferExpr :: Expr -> GenM Type
inferExpr x = case x of
  EVar ident -> getVarType ident
  ELitInt integer -> return Int
  ELitTrue -> return Bool
  ELitFalse -> return Bool
  EApp ident exprs ->
    getFunType ident >>= (\(Fun t _) -> return t)
  EString string -> return Str
  Neg expr -> return Int
  Not expr -> return Bool
  EMul expr1 mulop expr2 -> return Int
  EAdd expr1 addop expr2 -> inferExpr expr1
  ERel expr1 relop expr2 -> return Bool
  EAnd expr1 expr2 -> return Bool
  EOr expr1 expr2 -> return Bool

genExpr :: Expr -> GenM Operand
genExpr x = case x of
  EVar ident -> loadVar ident
  ELitInt integer -> return $ LitInt integer
  ELitTrue -> return $ LitInt 1
  ELitFalse -> return $ LitInt 0
  EApp ident exprs -> do
    vs <- mapM genExpr exprs
    mapM_ emitParam vs
    emitCall ident
  EString string -> do
    emitParam $ LitInt . toInteger $ (length string + 1)
    emitParam $ LitInt 4
    allocated <- emitCallExternal "calloc"
    sequence_ [emitWrite allocated (offset-1) value | (offset, value) <- zip [1..(length string)] (map (LitInt . toInteger. fromEnum) string)]
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
  EAdd expr1 addop expr2 -> do
    type_ <- inferExpr expr1
    case type_ of
      Str -> genAddStr expr1 expr2
      Int ->
        let {op = case addop of
          Plus -> QAdd
          Minus -> QSub}
        in do
          e1 <- genExpr expr1
          e2 <- genExpr expr2
          emitBin QBinOp op e1 e2
      _ -> fail "wrong types in expression"
  ERel expr1 relop expr2 ->
    let {op = case relop of
      LTH -> L
      AbsLatte.LE -> IR.LE
      GTH -> G
      AbsLatte.GE -> IR.GE
      EQU -> E
      AbsLatte.NE -> IR.NE}
    in do
      e1 <- genExpr expr1
      e2 <- genExpr expr2
      emitBin QCompOp op e1 e2
  EAnd expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 freshLabel
    emit $ QGotoBool e1 l1 l2
    emitLabel l1
    e2 <- genExpr expr2
    emit $ QAnd e1 e1 e2
    emit $ QGoto l2
    emitLabel l2
    return e1
  EOr expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 freshLabel
    emit $ QGotoBool e1 l2 l1
    emitLabel l1
    e2 <- genExpr expr2
    emit $ QAnd e1 e1 e2
    emit $ QGoto l2
    emitLabel l2
    return  e1

genAddStr :: Expr -> Expr -> GenM Operand
genAddStr expr1 expr2 = do
  e1 <- genExpr expr1
  e2 <- genExpr expr2
  emitParam e1
  l1 <- emitCallExternal "strlen"
  emitParam e2
  l2 <- emitCallExternal "strlen"
  st <- emitBin QBinOp QAdd l1 l2
  st2 <- emitBin QBinOp QAdd st (LitInt 1)
  emitParam st2
  allocated <- emitCallExternal "malloc"
  emitParam allocated
  emitParam e1
  emitCallExternal "strcpy"
  emitParam allocated
  emitParam e2
  emitCallExternal "strcat"
  return allocated

genStmts :: [Stmt] -> GenM ()
genStmts l =
  case l of
    h:t -> do
      env <- genStmt h
      local (const env) $ genStmts t
    [] -> return ()

genDecls :: Type -> [Item] -> GenM GenEnv
genDecls type_ l =
  case l of
    h:t -> do
      env <- genDecl type_ h
      local (const env) $ genDecls type_ t
    [] -> ask

genStmt :: Stmt -> GenM GenEnv
genStmt x = case x of
  Empty -> ask
  BStmt (Block stmts) -> do
    genStmts stmts
    ask
  Decl type_ items -> genDecls type_ items
  Ass ident expr -> do
    e <- genExpr expr
    storeVar ident e
    ask
  Incr ident -> do
    val <- loadVar ident
    res <- emitBin QBinOp QAdd val (LitInt 1)
    storeVar ident res
    ask
  Decr ident -> do
    val <- loadVar ident
    res <- emitBin QBinOp QSub val (LitInt 1)
    storeVar ident res
    ask
  Ret expr -> genExpr expr >>= (emit . QRet) >> ask
  VRet -> emit QVRet >> ask
  Cond expr stmt -> do
    [l1, l2] <- replicateM 2 freshLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    emitLabel l1
    genStmt stmt
    emit $ QGoto l2
    emitLabel l2
    ask
  CondElse expr stmt1 stmt2 -> do
    [l1, l2, l3] <- replicateM 3 freshLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    emitLabel l1
    genStmt stmt1
    emit $ QGoto l3
    emitLabel l2
    genStmt stmt2
    emit $ QGoto l3
    emitLabel l3
    ask
  While expr stmt -> do
    [l1, l2] <- replicateM 2 freshLabel
    e1 <- genExpr expr
    emit $ QGotoBool e1 l1 l2
    emitLabel l1
    genStmt stmt
    e2 <- genExpr expr
    emit $ QGotoBool e2 l1 l2
    emitLabel l2
    ask
  SExp expr -> do
    genExpr expr
    ask

splitBlocks :: [Dynamic] -> [[Dynamic]]
splitBlocks list =
  let {
    splt l cur acc =
      case l of
        h : t -> case (fromDynamic :: Dynamic -> Maybe (Quad Operand C O)) h of
          Just _ -> splt t [h] (reverse cur : acc)
          Nothing -> splt t (h: cur) acc
        [] -> reverse acc ++ [reverse cur]}
  in tail $ splt list [] []

makeBlock :: [Dynamic] -> (Label, Graph (Quad Operand) C C)
makeBlock l =
  let flt fun = map fromJust . filter (Nothing /=) . map fun
      entry = head . flt (fromDynamic :: Dynamic -> Maybe (Quad Operand C O)) $ l
      exit =  head . flt (fromDynamic :: Dynamic -> Maybe (Quad Operand O C)) $ l
      --exit = QError
      middle = flt (fromDynamic :: Dynamic -> Maybe (Quad Operand O O)) l
      (QLabel label) = entry
  in (label, mkFirst entry H.<*> mkMiddles middle H.<*> mkLast exit)

funType :: TopDef -> (Ident, Type)
funType x = case x of
  FnDef t ident args _ ->
    (ident, Fun t $ map (\(Arg t _) -> t) args)

makeFun :: GenEnv -> Type -> Ident -> [Arg] -> GenM a ->
  QFunDef (Label, Graph (Quad Operand) C C)
makeFun initEnv type_ ident args gen =
  let fntype = Fun type_ (map (\(Arg t _) -> t) args)
      vars = map (\(Arg t ident, i) -> insertVar ident (Param i) t)
        $ zip args [0..length args - 1]
      env = foldr (.) id vars initEnv
      state = newState
      (s, output) = execRWS gen env state
      (labels, blocks) = unzip . map makeBlock . splitBlocks $ output
      entry = head labels
      graph = foldl (|*><*|) emptyClosedGraph blocks
    in QFunDef ident fntype (entry, graph) (toInteger . length $ args)

checkIfZero :: Operand -> GenM ()
checkIfZero reg = do
  [l1, l2] <- replicateM 2 freshLabel
  emit $ QGotoBool reg l2 l1
  emitLabel l1
  emit QError
  emitLabel l2

predefPrintInt :: QFunDef (Label, Graph (Quad Operand) C C)
predefPrintInt =
  let
    parm = Ident "i"
    code = do
      label <- freshLabel
      emitLabel label
      x <- loadVar parm
      form <- genExpr $ EString "%d"
      emitParam form
      emitParam x
      emitCallExternal "printf"
      emitParam form
      emitCallExternal "free"
      emit QVRet
  in makeFun newEnv Void (Ident "printInt") [Arg Int parm] code

predefPrintString :: QFunDef (Label, Graph (Quad Operand) C C)
predefPrintString =
  let
    parm = Ident "s"
    code = do
      label <- freshLabel
      emitLabel label
      x <- loadVar parm
      emitParam x
      emitCallExternal "puts"
      emit QVRet
  in makeFun newEnv Void (Ident "printString") [Arg Str parm] code

predefReadInt :: QFunDef (Label, Graph (Quad Operand) C C)
predefReadInt =
  let
    code = do
      label <- freshLabel
      emitLabel label
      x <- emitAlloca
      form <- genExpr $ EString "%d"
      emitParam form
      emitParam x
      read_ <- emitCallExternal "scanf"
      emitParam form
      emitCallExternal "free"
      checkIfZero read_
      res <- emitLoad x
      emit $ QRet res
  in makeFun newEnv Int (Ident "readInt") [] code

predefReadString :: QFunDef (Label, Graph (Quad Operand) C C)
predefReadString =
  let
    code = do
      label <- freshLabel
      emitLabel label
      emitParam $ LitInt 256
      dest <- emitCallExternal "malloc"
      emitParam dest
      res <- emitCallExternal "gets"
      checkIfZero res
      emit $ QRet res
  in makeFun newEnv Str (Ident "readString") [] code

predefError :: QFunDef (Label, Graph (Quad Operand) C C)
predefError =
  let {code = do
    label <- freshLabel
    emitLabel label
    emit QError
  }
  in makeFun newEnv Void (Ident "error") [] code

genFun :: GenEnv -> TopDef -> QFunDef (Label, Graph (Quad Operand) C C)
genFun initEnv (FnDef type_ ident args block) =
  let {gen = do
    label <- freshLabel
    emitLabel label
    genStmt $ BStmt block
    emit QError}
  in makeFun initEnv type_ ident args gen

genProgram :: Program -> [QFunDef (Label, Graph (Quad Operand) C C)]
genProgram (Program topdefs) =
  let defs = topdefs ++ Frontend.predefs
      initEnv = foldl insertFunType newEnv $ map funType defs
  in map (genFun initEnv) topdefs ++
    [predefPrintInt, predefPrintString, predefError,
      predefReadString, predefReadInt]

instance ShowLinRepr (Label, Graph (Quad Operand) C C) where
  showlr (_, g) = showGraph show g
