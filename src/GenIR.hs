{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GenIR
  (QFunDef(..), genProgram)
  where

import           AbsLatte
import           Compiler.Hoopl            (C, Graph, Label, O, Unique,
                                            UniqueMonad, emptyClosedGraph,
                                            freshLabel, freshUnique, mkFirst,
                                            mkLast, mkMiddles, showGraph,
                                            (|*><*|))
import qualified Compiler.Hoopl            as H ((<*>))
import           Control.Monad
import           Control.Monad.RWS
import qualified Data.Map                  as Map
import           Data.Maybe
import           Frontend
import           Generics.Deriving.Copoint (gcopoint)
import           IR
import           Text.Printf


data GenState = GenState {
  uniqueC    :: Unique,
  regCounter:: Integer
  }

data GenEnv = GenEnv {
  varInfo   :: Map.Map Ident (Operand, VType),
  globalEnv :: GlobalEnv,
  inClass   :: Maybe ClassSig
}

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

newEnv :: GlobalEnv -> GenEnv
newEnv genv =
  GenEnv { varInfo = Map.empty, globalEnv = genv, inClass = Nothing }


instance PrintfArg Ident where
  formatArg (Ident s) _ = showString s

getVarLoc :: Ident -> GenM Operand
getVarLoc ident = do
  env <- ask
  case Map.lookup ident (varInfo env) of
    Just (op, _) -> return op
    Nothing -> fail $ printf "internal error: variable %s not found" ident

computeFieldOffset :: ClassSig -> Ident -> Maybe Int
computeFieldOffset classSig ident =
  let allfields = map fst $ listfields (Just classSig)
      prefix = takeWhile (ident /=) allfields
      res = length prefix in
  if res == length allfields then Nothing else Just res
  where
    listfields (Just cs) = listfields (super cs) ++ fields cs
    listfields Nothing = []

getFieldOffset :: GlobalEnv -> VType -> Ident -> Int
getFieldOffset genv type_ ident =
  fromMaybe (error "internal error - field not found") comp -- TODO?
  where
    comp = do
      className <- extractClassName type_
      classSig <- findClass genv className
      computeFieldOffset classSig ident

insertVar ::  Ident -> Operand -> VType -> GenEnv -> GenEnv
insertVar ident op type_ env =
  env{varInfo = Map.insert ident (op, type_) (varInfo env)}


emit :: PackIns (Quad Operand e x) => Quad Operand e x -> GenM ()
emit a = tell [packIns a]

emitBin :: (Operand -> a -> Operand -> Operand -> Quad Operand O O) -> a ->
  Operand -> Operand -> GenM Operand
emitBin con op r1 r2 = do
  dest <- newReg
  emit $ con dest op r1 r2
  return dest

emitUn :: (Operand -> Operand -> Quad Operand O O) -> Operand -> GenM Operand
emitUn con r = do
  dest <- newReg
  emit $ con dest r
  return dest

emitParam :: Operand -> GenM ()
emitParam operand = emit $ QParam operand

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

-- emitAlloca :: GenM Operand
-- emitAlloca = do
--   new <- newReg
--   emit $ QAlloca new
--   return new

emitLabel :: Label -> GenM ()
emitLabel = emit . QLabel

emitStore :: Operand -> Operand -> GenM ()
emitStore dest src = emit $ QStore dest src

emitGetFieldAddress :: Operand -> VType -> Ident -> GenM Operand
emitGetFieldAddress base type_ ident = do
  genv <- globalEnv <$> ask
  let offset = 4 + 4 * getFieldOffset genv type_ ident
  emitBin QBinOp QAdd base (LitInt $ toInteger offset)

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
loadVar =
  getVarLoc

storeVar :: Ident -> Operand -> GenM ()
storeVar ident val = do
  reg <- getVarLoc ident
  emit $ QCopy reg val

genInitClass :: ClassSig -> GenM Operand
genInitClass classSig = do
  let fields = [] -- TODO
  let size = 4 + 4 * length fields
  emitParam $ LitInt $ toInteger size
  allocated <- emitCallExternal "malloc"
  -- TODO vtable
  forM_ fields (gen allocated)
  return allocated
  where
    gen base (ident, type_) = do
       value <- genExpr (defaultValue type_)
       field <- emitGetFieldAddress base (Class () $ name classSig) ident
       emitStore field value

genCall :: Ident -> GenM Operand
genCall ident =
  if isPredef ident then
    let Ident s = ident
    in emitCallExternal s
  else
    emitCall ident

genDecl :: VType -> Item VType -> GenM GenEnv
genDecl type_ item = do
  env <- ask
  let {(e, ident) = case item of
    NoInit x ident ->
      (fmap (const x) (defaultValue type_), ident)
    Init _ ident expr -> (expr, ident)}
  uniq <- freshUnique
  let (Ident s) = ident
  let new = Reg $ printf "v%d_%s" uniq s
  r <- genExpr e
  --emitStore new r
  emit $ QCopy new r
  return $ insertVar ident new type_ env

defaultValue :: VType -> Expr VType
defaultValue t = case t of
  Int _  -> ELitInt intType 0
  Bool _ -> ELitFalse boolType
  Str _  -> EString stringType ""
  Class _ ident -> ENew (Class () ident) ident
  Void _ -> error "internal error: default value of type void doesn't exist"

genExpr :: Expr VType -> GenM Operand
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
    let corrected = drop 1 (take (length string - 1) string)
    emitParam $ LitInt . toInteger $ (length corrected + 1)
    emitParam $ LitInt 4
    allocated <- emitCallExternal "calloc"
    sequence_ [emitWrite allocated (offset-1) value | (offset, value) <-
                zip [1..(length corrected)] (map (LitInt . toInteger. fromEnum) corrected)]
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
      Div _   -> QDiv
      Mod _   -> QMod}
    in do
      e1 <- genExpr expr1
      e2 <- genExpr expr2
      emitBin QBinOp op e1 e2
  EAdd type_ expr1 addop expr2 ->
    case type_ of
      Str _ -> genAddStr expr1 expr2
      Int _ ->
        let {op = case addop of
          Plus _  -> QAdd
          Minus _ -> QSub}
        in do
          e1 <- genExpr expr1
          e2 <- genExpr expr2
          emitBin QBinOp op e1 e2
      _ -> error "internal error: wrong types in expression"
  ERel _ expr1 relop expr2 -> do
    let t1 = gcopoint expr1
    case t1 of
      Str _ -> genCmpString relop expr1 expr2
      Int _ ->
        let {op = case relop of
          LTH _         -> L
          AbsLatte.LE _ -> IR.LE
          GTH _         -> G
          AbsLatte.GE _ -> IR.GE
          EQU _         -> E
          AbsLatte.NE _ -> IR.NE}
        in do
          e1 <- genExpr expr1
          e2 <- genExpr expr2
          emitBin QCompOp op e1 e2
      _ -> genCmpPhysicalEq relop expr1 expr2
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
  ENull _ _ ->
    return $ LitInt 0
  EThis _ ->
    return $ Param 0
  ENew _ ident -> do
    genv <- globalEnv <$> ask
    case findClass genv ident of
      Just classSig -> genInitClass classSig
      Nothing -> error $ "internal error: class not found" ++ show ident
  EField _ expr ident -> do
    e <- genExpr expr
    fieldA <- emitGetFieldAddress e (gcopoint expr) ident
    emitLoad fieldA


genCmpPhysicalEq :: RelOp VType -> Expr VType -> Expr VType -> GenM Operand
genCmpPhysicalEq relop e1 e2 = do
  s1 <- genExpr e1
  s2 <- genExpr e2
  emitBin QCompOp op s1 s2
  where
    op = case relop of
      EQU _ -> E
      AbsLatte.NE _ -> IR.NE
      _ ->
        error "internal error - only equality comparisons for classes and bools"

genCmpString :: RelOp VType -> Expr VType -> Expr VType -> GenM Operand
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

genAddStr :: Expr VType -> Expr VType -> GenM Operand
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

genStmts :: [Stmt VType] -> GenM ()
genStmts l =
  case l of
    h:t -> do
      env <- genStmt h
      local (const env) $ genStmts t
    [] -> return ()

genDecls :: VType -> [Item VType] -> GenM GenEnv
genDecls type_ l =
  case l of
    h:t -> do
      env <- genDecl type_ h
      local (const env) $ genDecls type_ t
    [] -> ask

genStmt :: Stmt VType -> GenM GenEnv
genStmt x = case x of
  Empty _ -> ask
  BStmt _ (Block _ stmts) -> do
    genStmts stmts
    ask
  Decl _ type_ items -> genDecls (void type_) items
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
  AssField _ expr1 ident expr2 -> do
    e1 <- genExpr expr1
    fieldA <- emitGetFieldAddress e1 (gcopoint expr1) ident
    e2 <- genExpr expr2
    emitStore fieldA e2
    ask
  IncrField _ expr ident -> do
    e <- genExpr expr
    fieldA <- emitGetFieldAddress e (gcopoint expr) ident
    fieldV <- emitLoad fieldA
    res <- emitBin QBinOp QAdd fieldV (LitInt 1)
    emitStore fieldA res
    ask
  DecrField _ expr ident -> do
    e <- genExpr expr
    fieldA <- emitGetFieldAddress e (gcopoint expr) ident
    fieldV <- emitLoad fieldA
    res <- emitBin QBinOp QSub fieldV (LitInt 1)
    emitStore fieldA res
    ask

splitBlocks :: [Ins Operand] -> [[Ins Operand]]
splitBlocks list =
  let {
    splt l cur acc =
      case l of
        h : t -> case h of
          Fst _ -> splt t [h] (reverse cur : acc)
          _     -> splt t (h: cur) acc
        [] -> reverse acc ++ [reverse cur]}
  in tail $ splt list [] []

makeBlock :: [Ins Operand] -> (Label, Graph (Quad Operand) C C)
makeBlock l =
  let fltFst (Fst _) = True
      fltFst _       = False
      fltMid (Mid _) = True
      fltMid _       = False
      fltLst (Lst _) = True
      fltLst _       = False
      Fst entry = head $ filter fltFst l
      Lst exit = head $ filter fltLst l
      middle = map (\(Mid x) -> x) $ filter fltMid l
      (QLabel label) = entry
  in (label, mkFirst entry H.<*> mkMiddles middle H.<*> mkLast exit)


makeFun :: GenEnv -> VType -> Ident -> [Arg VType] -> GenM b ->
  QFunDef (Label, Graph (Quad Operand) C C)
makeFun initEnv type_ ident args gen =
  let fntype = makeFunSig type_ args
      paramShift = if isJust $ inClass initEnv then 1 else 0
      vars = map (\(Arg _ t ident, i) ->
                  insertVar ident (Param (i+paramShift)) $ void t)
        $ zip args [0..length args - 1]
      env = foldr (.) id vars initEnv
      state = newState
      (_, output) = execRWS gen env state
      (labels, blocks) = unzip . map makeBlock . splitBlocks $ output
      entry = head labels
      graph = foldl (|*><*|) emptyClosedGraph blocks
    in QFunDef ident fntype (entry, graph) (toInteger . length $ args)

-- checkIfZero :: Operand -> GenM ()
-- checkIfZero reg = do
--   [l1, l2] <- replicateM 2 freshLabel
--   emit $ QGotoBool reg l2 l1
--   emitLabel l1
--   emit QError
--   emitLabel l2

genFun :: GenEnv -> VType -> Ident -> [Arg VType] -> Block VType ->
  QFunDef (Label, Graph (Quad Operand) C C)
genFun initEnv type_ ident args block =
  let {gen = do
    label <- freshLabel
    emitLabel label
    genStmt $ BStmt voidType block
    when (type_ == Void ()) $ emit QVRet}
  in makeFun initEnv (void type_) ident args gen

genTopDef :: GlobalEnv -> TopDef VType -> [QFunDef (Label, Graph (Quad Operand) C C)]
genTopDef genv (FnDef _ type_ ident args block) =
  let env = newEnv genv in
  [genFun env (void type_) ident args block]
genTopDef genv (ClassDef _ ident _ classels) =
  let env = (newEnv genv) {inClass = findClass genv ident} in
  concatMap (genClassEl env) classels


genClassEl :: GenEnv -> ClassEl VType -> [QFunDef (Label, Graph (Quad Operand) C C)]
genClassEl _ _ = [] -- TODO

genProgram :: (Program VType, GlobalEnv) -> [QFunDef (Label, Graph (Quad Operand) C C)]
genProgram (Program _ topdefs, genv) =
  concatMap (genTopDef genv) topdefs

instance ShowLinRepr (Label, Graph (Quad Operand) C C) where
  showlr (_, g) = showGraph show g
