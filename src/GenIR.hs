{-# LANGUAGE FlexibleInstances, GADTs, FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GenIR
  (QFunDef(..), genProgram)
  where

import IR
import qualified Data.Map as Map
import AbsLatte hiding (Type(..))
import qualified AbsLatte (Type(..))
import Frontend (Type(..), transType)
import Control.Monad
import Control.Monad.RWS
import Text.Printf
import qualified Frontend (predefs)
import Compiler.Hoopl (Label, UniqueMonad, Unique,
 freshUnique, freshLabel, C, O, Graph, (|*><*|),
  mkFirst, mkLast, mkMiddles, emptyClosedGraph, showGraph)
import qualified Compiler.Hoopl as H ((<*>))
import Data.Maybe
import qualified Frontend -- for printfArg instance


data VarLoc = Stack Operand | Param Int

newtype IsPredef = IsPredef Bool

data GenState = GenState {
  uniqueC :: Unique,
  regCounter:: Integer
  }

data FunInfo  = FunInfo {
  funIdent :: Ident,
  funType :: Type,
  isPredef :: Bool
}

data GenEnv = GenEnv {
  varInfo :: Map.Map Ident (VarLoc, Type),
  funInfo :: Map.Map Ident FunInfo}

type GenM = RWS GenEnv [Ins Operand] GenState

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

insertFunInfo :: GenEnv -> FunInfo -> GenEnv
insertFunInfo env info =
  env{funInfo = Map.insert (funIdent info) info $ funInfo env}

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
    Just x -> return $ funType x
    Nothing -> fail $ printf "internal error: function %s not found" ident

getFunInfo :: Ident -> GenM FunInfo
getFunInfo ident = do
  env <- ask
  case Map.lookup ident $ funInfo env of
    Just x -> return x
    Nothing -> fail $ printf "internal error: function %s not found" ident

insertVar ::  Ident -> VarLoc -> Type -> GenEnv -> GenEnv
insertVar ident varloc type_ env =
  env{varInfo = Map.insert ident (varloc, type_) (varInfo env)}


emit :: PackIns (Quad Operand e x) => Quad Operand e x -> GenM ()
emit a = tell [packIns a]

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
  dest <- emitBin QBinOp QAdd base (LitInt . toInteger $(offset))
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


genCall :: Ident -> GenM Operand
genCall ident = do
  info <- getFunInfo ident
  if isPredef info then
    let Ident s = ident
    in emitCallExternal s
  else
    emitCall ident

genDecl :: Type -> Item a -> GenM GenEnv
genDecl type_ item = do
  env <- ask
  let {(e, ident) = case item of
    NoInit x ident -> (fmap (const x) (fromJust $ defaultValue type_), ident)
    Init _ ident expr -> (expr, ident)}
  uniq <- freshUnique
  let (Ident s) = ident
  let new = Reg $ printf "v%d_%s" uniq s
  let loc = Stack new
  r <- genExpr e
  --emitStore new r
  emit $ QCopy new r
  return $ insertVar ident loc type_ env

defaultValue :: Type -> Maybe (Expr ())
defaultValue t = case t of
  Int -> Just $ ELitInt () 0
  Bool -> Just $ ELitFalse ()
  Str -> Just $ EString () ""
  _ -> Nothing

inferExpr :: Expr a -> GenM Type
inferExpr x = case x of
  EVar _ ident -> getVarType ident
  ELitInt _ integer -> return Int
  ELitTrue _ -> return Bool
  ELitFalse _ -> return Bool
  EApp _ ident exprs ->
    getFunType ident >>= (\(Fun t _) -> return t)
  EString _ string -> return Str
  Neg _ expr -> return Int
  Not _ expr -> return Bool
  EMul _ expr1 mulop expr2 -> return Int
  EAdd _ expr1 addop expr2 -> inferExpr expr1
  ERel _ expr1 relop expr2 -> return Bool
  EAnd _ expr1 expr2 -> return Bool
  EOr _ expr1 expr2 -> return Bool

genExpr :: Expr a -> GenM Operand
genExpr x = case x of
  EVar _ ident -> loadVar ident
  ELitInt _ integer -> return $ LitInt integer
  ELitTrue _ -> return $ LitInt 1
  ELitFalse _ -> return $ LitInt 0
  EApp _ ident exprs -> do
    vs <- mapM genExpr exprs
    mapM_ emitParam vs
    genCall ident
  EString _ string -> do
    emitParam $ LitInt . toInteger $ (length string + 1)
    emitParam $ LitInt 4
    allocated <- emitCallExternal "calloc"
    sequence_ [emitWrite allocated (offset-1) value | (offset, value) <- zip [1..(length string)] (map (LitInt . toInteger. fromEnum) string)]
    return allocated
  Neg _ expr -> do
    e <- genExpr expr
    emitUn QNeg e
  Not _ expr -> do
    e <- genExpr expr
    emitUn QNot e
  EMul _ expr1 mulop expr2 ->
    let {op = case mulop of
      Times _ -> QMul
      Div _ -> QDiv
      Mod _ -> QMod}
    in do
      e1 <- genExpr expr1
      e2 <- genExpr expr2
      emitBin QBinOp op e1 e2
  EAdd _ expr1 addop expr2 -> do
    type_ <- inferExpr expr1
    case type_ of
      Str -> genAddStr expr1 expr2
      Int ->
        let {op = case addop of
          Plus _ -> QAdd
          Minus _ -> QSub}
        in do
          e1 <- genExpr expr1
          e2 <- genExpr expr2
          emitBin QBinOp op e1 e2
      _ -> fail "wrong types in expression"
  ERel _ expr1 relop expr2 -> do
    t1 <- inferExpr expr1
    case t1 of
      Str -> genCmpString relop expr1 expr2
      _ ->
        let {op = case relop of
          LTH _ -> L
          AbsLatte.LE _ -> IR.LE
          GTH _ -> G
          AbsLatte.GE _ -> IR.GE
          EQU _ -> E
          AbsLatte.NE _ -> IR.NE}
        in do
          e1 <- genExpr expr1
          e2 <- genExpr expr2
          emitBin QCompOp op e1 e2
  EAnd _ expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 freshLabel
    emit $ QGotoBool e1 l1 l2
    emitLabel l1
    e2 <- genExpr expr2
    emit $ QAnd e1 e1 e2
    emit $ QGoto l2
    emitLabel l2
    return e1
  EOr _ expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 freshLabel
    emit $ QGotoBool e1 l2 l1
    emitLabel l1
    e2 <- genExpr expr2
    emit $ QOr e1 e1 e2
    emit $ QGoto l2
    emitLabel l2
    return  e1

genCmpString :: RelOp a -> Expr a -> Expr a -> GenM Operand
genCmpString relop e1 e2 = do
  s1 <- genExpr e1
  s2 <- genExpr e2
  emitParam s1
  emitParam s2
  res <- emitCallExternal "strcmp"
  emitBin QCompOp op res (LitInt 0)
  where
    op = case relop of
      EQU _ -> E
      AbsLatte.NE _ -> IR.NE
      _ ->
        error "internal error - only equality comparisons for strings"

genAddStr :: Expr a -> Expr a -> GenM Operand
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

genStmts :: [Stmt a] -> GenM ()
genStmts l =
  case l of
    h:t -> do
      env <- genStmt h
      local (const env) $ genStmts t
    [] -> return ()

genDecls :: Type -> [Item a] -> GenM GenEnv
genDecls type_ l =
  case l of
    h:t -> do
      env <- genDecl type_ h
      local (const env) $ genDecls type_ t
    [] -> ask

genStmt :: Stmt a -> GenM GenEnv
genStmt x = case x of
  Empty _ -> ask
  BStmt _ (Block _ stmts) -> do
    genStmts stmts
    ask
  Decl _ type_ items -> genDecls (transType type_) items
  Ass _ ident expr -> do
    e <- genExpr expr
    storeVar ident e
    ask
  Incr _ ident -> do
    val <- loadVar ident
    res <- emitBin QBinOp QAdd val (LitInt 1)
    storeVar ident res
    ask
  Decr _ ident -> do
    val <- loadVar ident
    res <- emitBin QBinOp QSub val (LitInt 1)
    storeVar ident res
    ask
  Ret _ expr -> genExpr expr >>= (emit . QRet) >> ask
  VRet _ -> emit QVRet >> ask
  Cond _ expr stmt -> do
    [l1, l2] <- replicateM 2 freshLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    emitLabel l1
    genStmt stmt
    emit $ QGoto l2
    emitLabel l2
    ask
  CondElse _ expr stmt1 stmt2 -> do
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
  While _ expr stmt -> do
    [l1, l2] <- replicateM 2 freshLabel
    e1 <- genExpr expr
    emit $ QGotoBool e1 l1 l2
    emitLabel l1
    genStmt stmt
    e2 <- genExpr expr
    emit $ QGotoBool e2 l1 l2
    emitLabel l2
    ask
  SExp _ expr -> do
    genExpr expr
    ask

splitBlocks :: [Ins Operand] -> [[Ins Operand]]
splitBlocks list =
  let {
    splt l cur acc =
      case l of
        h : t -> case h of
          Fst _ -> splt t [h] (reverse cur : acc)
          _ -> splt t (h: cur) acc
        [] -> reverse acc ++ [reverse cur]}
  in tail $ splt list [] []

makeBlock :: [Ins Operand] -> (Label, Graph (Quad Operand) C C)
makeBlock l =
  let fltFst (Fst _) = True
      fltFst _ = False
      fltMid (Mid _) = True
      fltMid _ = False
      fltLst (Lst _) = True
      fltLst _ = False
      Fst entry = head $ filter fltFst l
      Lst exit = head $ filter fltLst l
      middle = map (\(Mid x) -> x) $ filter fltMid l
      (QLabel label) = entry
  in (label, mkFirst entry H.<*> mkMiddles middle H.<*> mkLast exit)

makeFunInfo :: Bool -> TopDef a -> FunInfo
makeFunInfo ispredef x = case x of
  FnDef _ t ident args _ -> FunInfo {
    funIdent = ident,
    funType = Fun (transType t) $ map (\(Arg _ t _) -> transType t) args,
    isPredef = ispredef}

makeFun :: GenEnv -> Type -> Ident -> [Arg a] -> GenM b ->
  QFunDef (Label, Graph (Quad Operand) C C)
makeFun initEnv type_ ident args gen =
  let fntype = Fun type_ (map (\(Arg _ t _) -> transType t) args)
      vars = map (\(Arg _ t ident, i) -> insertVar ident (Param i) $ transType t)
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



genFun :: GenEnv -> TopDef a -> QFunDef (Label, Graph (Quad Operand) C C)
genFun initEnv (FnDef x type_ ident args block) =
  let {gen = do
    label <- freshLabel
    emitLabel label
    genStmt $ BStmt x block
    case defaultValue $ transType type_ of
      Just expr -> do
        e <- genExpr expr
        emit $ QRet e
      Nothing -> emit $ QVRet}
  in makeFun initEnv (transType type_) ident args gen

genProgram :: Program a -> [QFunDef (Label, Graph (Quad Operand) C C)]
genProgram (Program _ topdefs) =
  let predefinfos = map (makeFunInfo True) Frontend.predefs
      infos = map (makeFunInfo False) topdefs
      initEnv = foldl insertFunInfo newEnv $ infos ++ predefinfos
  in map (genFun initEnv) topdefs

instance ShowLinRepr (Label, Graph (Quad Operand) C C) where
  showlr (_, g) = showGraph show g
