module IR
  (Operand, Label, Quadruple, BinOp, CompOp, QFunDef, genProgram)
  where


import qualified Data.Map as Map
import AbsLatte
import Control.Monad
import Control.Monad.RWS
import Text.Printf

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
data VarLoc = Stack Integer

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
  QBasePointer Operand

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
     QBasePointer d -> printf "  %s = gen bp" d
     QLabel l -> printf "%s:" l

data GenState = GenState {
  labelCounter :: Integer,
  regCounter:: Integer,
  stackOffset :: Integer
  }

data GenEnv = GenEnv {
  varInfo :: Map.Map Ident (VarLoc, Type),
  basePointer :: Operand }

type GenM a = RWS GenEnv [Quadruple] GenState a

getStackLocation :: GenM VarLoc
getStackLocation = do
  state <- get
  let offset = stackOffset state -1
  put state{stackOffset = offset}
  return $ Stack offset

newState :: GenState
newState =
  GenState {labelCounter = 0, regCounter = 0, stackOffset = 0}

newEnv :: Operand -> GenEnv
newEnv bp =
  GenEnv {basePointer = bp, varInfo = Map.empty}

getVarLoc :: Ident -> GenM VarLoc
getVarLoc ident = do
  env <- ask
  case Map.lookup ident (varInfo env) of
    Just (loc, _) -> return loc
    Nothing -> fail "error variable not found"

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
  dest <- emitBin QBinOp QSub base (LitInt . toInteger $((-4)*offset))
  emit $ QStore dest value

emitLoadAddress :: VarLoc -> GenM Operand
emitLoadAddress varloc = do
  env <- ask
  case varloc of
    Stack offset ->
      emitBin QBinOp QSub (basePointer env) (LitInt . toInteger $((-4)*offset))



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

getAddr :: Ident -> GenM Operand
getAddr ident = do
  varloc <- getVarLoc ident
  emitLoadAddress varloc

genDecl :: Type -> Item -> GenM GenEnv
genDecl type_ item = do
  env <- ask
  loc <- getStackLocation
  case item of
    NoInit ident ->
      return $ insertVar ident loc type_ env
    Init ident expr -> do
      reg <- emitLoadAddress loc
      e <- genExpr expr
      emit $ QStore reg e
      return $ insertVar ident loc type_ env


genExpr :: Expr -> GenM Operand
genExpr x = case x of
  EVar ident -> do
    a <- getAddr ident
    emitUn QLoad a
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
    reg <- getAddr ident
    e <- genExpr expr
    emit $ QStore reg e
    ask
  Incr ident -> do
    reg <- getAddr ident
    val <- emitUn QLoad reg
    res <- emitBin QBinOp QAdd val (LitInt 1)
    emit $ QStore reg res
    ask
  Decr ident -> do
    reg <- getAddr ident
    val <- emitUn QLoad reg
    res <- emitBin QBinOp QAdd val (LitInt 1)
    emit $ QStore reg res
    ask
  Ret expr -> genExpr expr >>= (emit . QRet) >> ask
  VRet -> emit QVRet >> ask
  Cond expr stmt -> do
    [l1, l2] <- replicateM 2 newLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    emit $ QLabel l1
    genStmt stmt
    emit $ QGoto l2
    emit $ QLabel l2
    ask
  CondElse expr stmt1 stmt2 -> do
    [l1, l2, l3] <- replicateM 3 newLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    emit $ QLabel l1
    genStmt stmt1
    emit $ QGoto l3
    emit $ QLabel l2
    genStmt stmt2
    emit $ QGoto l3
    emit $ QLabel l3
    ask
  While expr stmt -> do
    [l1, l2] <- replicateM 2 newLabel
    e1 <- genExpr expr
    emit $ QGotoBool e1 l1 l2
    emit $ QLabel l1
    genStmt stmt
    e2 <- genExpr expr
    emit $ QGotoBool e2 l1 l2
    emit $ QLabel l2
    ask
  SExp expr -> do
    genExpr expr
    ask

data QFunDef = QFunDef Ident Type [Quadruple] Integer

instance Show QFunDef where
  show (QFunDef (Ident ident) type_ quads _) =
    printf "function %s {\n%s}" ident $ unlines (map show quads)

genFun :: TopDef -> QFunDef
genFun (FnDef type_ ident args block) =
  let fntype = Fun type_ (map (\(Arg t _) -> t) args)
      bp = Reg "bp"
      gen = do
        emit $ QBasePointer bp
        genStmt (BStmt block)
      vars = map (\(Arg t ident, i) -> insertVar ident (Stack $ toInteger i) t)
        $ zip args [2..length args + 1]
      env = foldr (.) id vars $ newEnv bp
      state = newState
      (s, output) = execRWS gen env state
    in QFunDef ident fntype output (- stackOffset s)

genProgram :: Program -> [QFunDef]
genProgram (Program topdefs) = map genFun topdefs
