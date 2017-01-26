module IR
  (Operand, Label, Quadruple, BinOp, CompOp, QFunDef, genProgram)
  where


import qualified Data.Map as Map
import AbsLatte
import Control.Monad
import Control.Monad.RWS
import Text.Printf
import qualified Frontend (predefs)

instance PrintfArg Ident where
  formatArg (Ident s) _ = showString s

data Operand = Reg String | LitInt Integer
instance Show Operand where
  show (Reg i) = i
  show (LitInt i) = show i
instance PrintfArg Operand where
  formatArg x _ = case x of
    Reg s -> showString s
    LitInt i -> shows i

data BinOp = QAdd | QSub | QMul | QDiv | QMod
instance PrintfArg BinOp where
  formatArg x _ = showString $ case x of
    QAdd -> "+"
    QSub -> "-"
    QMul -> "*"
    QDiv -> "/"
    QMod -> "%"
data CompOp = L | LE | G | GE | E | NE
instance PrintfArg CompOp where
  formatArg x _ = showString $ case x of
    L -> "<"
    IR.LE -> "<="
    G -> ">"
    IR.GE -> ">="
    E -> "=="
    IR.NE -> "!="


newtype Label = Label String deriving (Show)
instance PrintfArg Label where
   formatArg (Label s) _ = showString s

data VarLoc = Stack Operand | Param Operand

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
  --QGotoComp Operand CompOp Operand Label Label |
  QGotoBool Operand Label Label |
  QParam Operand |
  QCall Operand Ident |
  QCallExternal Operand String |
  QLabel Label |
  QPhi Operand Operand Operand |
  QVRet |
  QRet Operand |
  QAlloca Operand |
  QError

instance Show Quadruple where
   show x = case x of
     QBinOp d op s1 s2 -> printf "  %s = %s %s %s" d s1 op s2
     QCompOp d op s1 s2 -> printf "  %s = %s %s %s" d s1 op s2
     QAnd d s1 s2 -> printf "  %s = %s && %s" d s1 s2
     QOr d s1 s2 -> printf "  %s = %s || %s" d s1 s2
     QNeg d s -> printf "  %s = -%s" d s
     QNot d s -> printf "  %s = !%s" d s
     QLoad d s -> printf "  %s = load %s" d s
     QStore d s -> printf "  store %s, %s" d s
     QCopy d s -> printf "  %s = %s" d s
     QGoto l -> printf "  goto %s" l
     QGotoBool r l1 l2 -> printf "  if %s goto %s else %s" r l1 l2
     QParam r -> printf "  param %s" r
     QCall d l -> printf "  %s = call %s" d (show l)
     QCallExternal d l -> printf "  %s = call external %s" d l
     QPhi d s1 s2 -> printf "  %s = phi(%s, %s)" d s1 s2
     QVRet -> "  ret"
     QRet r -> printf "  ret %s" r
     QLabel l -> printf "%s:" l
     QAlloca d -> printf "  %s = alloca" d
     QError -> printf "  error()"

data GenState = GenState {
  labelCounter :: Integer,
  regCounter:: Integer
  }

data GenEnv = GenEnv {
  varInfo :: Map.Map Ident (VarLoc, Type),
  funInfo :: Map.Map Ident Type}

type GenM a = RWS GenEnv [Quadruple] GenState a

newState :: GenState
newState =
  GenState {labelCounter = 0, regCounter = 0}

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

emitCall :: Ident -> GenM Operand
emitCall ident = do
  dest <- newReg
  tell [QCall dest ident]
  return dest

emitCallExternal :: String -> GenM Operand
emitCallExternal str = do
  dest <- newReg
  tell [QCallExternal dest str]
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

newLabel :: GenM Label
newLabel = do
  state <- get
  let number = labelCounter state
  put state{labelCounter = number+1}
  return $ Label ("l" ++ show number)


loadVar :: Ident -> GenM Operand
loadVar ident = do
  loc <- getVarLoc ident
  case loc of
    Stack reg -> emitLoad reg
    Param reg -> return reg

storeVar :: Ident -> Operand -> GenM()
storeVar ident val = do
  loc <- getVarLoc ident
  case loc of
    Stack reg -> emitStore reg val
    Param _ -> fail "internal error: assignment to parameter"


genDecl :: Type -> Item -> GenM GenEnv
genDecl type_ item = do
  env <- ask
  new <- emitAlloca
  let loc = Stack new
  let {(e, ident) = case item of
    NoInit ident -> (default_ type_, ident)
    Init ident expr -> (expr, ident)}
  r <- genExpr e
  emitStore new r
  return $ insertVar ident loc type_ env
  where {default_ t = case t of
    Int -> ELitInt 0
    Bool -> ELitFalse
    Str -> EString ""}

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
    [l1, l2] <- replicateM 2 newLabel
    emit $ QGotoBool e1 l1 l2
    emitLabel l1
    e2 <- genExpr expr2
    e3 <- emitAnd e1 e2
    emit $ QGoto l2
    emitLabel l2
    emitPhi e1 e2
  EOr expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 newLabel
    emit $ QGotoBool e1 l2 l1
    emitLabel l1
    e2 <- genExpr expr2
    e3 <- emitAnd e1 e2
    emit $ QGoto l2
    emitLabel l2
    emitPhi e1 e2

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
    [l1, l2] <- replicateM 2 newLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    emitLabel l1
    genStmt stmt
    emit $ QGoto l2
    emitLabel l2
    ask
  CondElse expr stmt1 stmt2 -> do
    [l1, l2, l3] <- replicateM 3 newLabel
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
    [l1, l2] <- replicateM 2 newLabel
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

data QFunDef = QFunDef Ident Type [Quadruple] Integer

instance Show QFunDef where
  show (QFunDef (Ident ident) type_ quads params) =
    printf "function %s(%d) {\n%s}" ident params $ unlines (map show quads)

funType :: TopDef -> (Ident, Type)
funType x = case x of
  FnDef t ident args _ ->
    (ident, Fun t $ map (\(Arg t _) -> t) args)

makeFun :: GenEnv -> Type -> Ident -> [Arg] -> GenM a -> QFunDef
makeFun initEnv type_ ident args gen =
  let fntype = Fun type_ (map (\(Arg t _) -> t) args)
      vars = map (\(Arg t ident, i) -> insertVar ident (Param $ Reg ("~p"++show i)) t)
        $ zip args [0..length args - 1]
      env = foldr (.) id vars initEnv
      state = newState
      (s, output) = execRWS gen env state
    in QFunDef ident fntype output (toInteger . length $ args)

checkIfZero :: Operand -> GenM ()
checkIfZero reg = do
  [l1, l2] <- replicateM 2 newLabel
  emit $ QGotoBool reg l2 l1
  emitLabel l1
  emit QError
  emitLabel l2

predefPrintInt :: QFunDef
predefPrintInt =
  let
    parm = Ident "i"
    code = do
      emitLabel $ Label "entry"
      x <- loadVar parm
      form <- genExpr $ EString "%d"
      emitParam form
      emitParam x
      emitCallExternal "printf"
      emitParam form
      emitCallExternal "free"
      emit QVRet
  in makeFun newEnv Void (Ident "printInt") [Arg Int parm] code

predefPrintString :: QFunDef
predefPrintString =
  let
    parm = Ident "s"
    code = do
      emitLabel $ Label "entry"
      x <- loadVar parm
      emitParam x
      emitCallExternal "puts"
      emit QVRet
  in makeFun newEnv Void (Ident "printString") [Arg Str parm] code

predefReadInt :: QFunDef
predefReadInt =
  let
    code = do
      emitLabel $ Label "entry"
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

predefReadString :: QFunDef
predefReadString =
  let
    code = do
      emitLabel $ Label "entry"
      emitParam $ LitInt 256
      dest <- emitCallExternal "malloc"
      emitParam dest
      res <- emitCallExternal "gets"
      checkIfZero res
      emit $ QRet res
  in makeFun newEnv Str (Ident "readString") [] code

predefError :: QFunDef
predefError =
  let {code = do
    emitLabel $ Label "entry"
    emit QError
  }
  in makeFun newEnv Void (Ident "error") [] code

genFun :: GenEnv -> TopDef -> QFunDef
genFun initEnv (FnDef type_ ident args block) =
  let {gen = do
    emitLabel $ Label "entry"
    genStmt $ BStmt block}
  in makeFun initEnv type_ ident args gen

genProgram :: Program -> [QFunDef]
genProgram (Program topdefs) =
  let defs = topdefs ++ Frontend.predefs
      initEnv = foldl insertFunType newEnv $ map funType defs
  in map (genFun initEnv) topdefs ++
    [predefPrintInt, predefPrintString, predefError,
      predefReadString, predefReadInt]
