{-# LANGUAGE GADTs #-}

module IR
  (Operand, Label, Quadruple, BinOp, CompOp, QFunDef, genProgram)
  where


import qualified Data.Map as Map
import AbsLatte
import Control.Monad
import Control.Monad.RWS
import Text.Printf


data Operand = Reg String | Phi String | Undef
  deriving (Ord, Eq)

instance Show Operand where
  show (Reg i) = i
  show (Phi i) = i
instance PrintfArg Operand where
  formatArg x _ = case x of
    Reg s -> showString s
    Phi s -> showString s

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


newtype Label = Label String deriving (Show, Eq, Ord)
instance PrintfArg Label where
   formatArg (Label s) _ = showString s
data VarLoc = Stack | Param


data Quadruple where
  QBinOp :: Operand -> BinOp -> Operand -> Operand -> Quadruple
  QCompOp :: Operand -> CompOp -> Operand -> Operand -> Quadruple
  QAnd :: Operand -> Operand -> Operand -> Quadruple
  QOr :: Operand -> Operand -> Operand -> Quadruple
  QNeg :: Operand -> Operand -> Quadruple
  QNot :: Operand -> Operand -> Quadruple
  QLoad :: Operand -> Operand -> Quadruple
  QStore :: Operand -> Operand -> Quadruple
  QCopy :: Operand -> Operand -> Quadruple
  QGoto :: Label -> Quadruple
  --QGotoComp Operand CompOp Operand Label Label |
  QGotoBool :: Operand -> Label -> Label -> Quadruple
  QParam :: Operand -> Quadruple
  QCall :: Operand -> Ident -> Quadruple
  QCallExternal :: Operand -> String -> Quadruple
  QLabel :: Label -> Quadruple
  QPhi :: Operand -> Operand -> Operand -> Quadruple
  QVRet :: Quadruple
  QRet :: Operand -> Quadruple
  QBasePointer :: Operand -> Quadruple
  QLitInt :: Operand -> Integer -> Quadruple
  QPhiPlaceholder :: Operand -> Operand -> Quadruple

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
     QLitInt d i -> printf "%s = %i" d i
-------------------------------------------------------------
---------- SSA CONSTRUCTION ZONE--------------------------------
------------------------------------------------------------
data PhiStruct = PhiStruct {operands :: [Operand], block :: Label}

data BlockStruct = BlockStruct {preds :: [Label], isSealed :: Bool}
newBlockStruct = BlockStruct {preds = [], isSealed = False}

data GenState = GenState {
  labelCounter :: Integer,
  regCounter:: Integer,
  phiCounter :: Integer ,
  stackOffset :: Integer,
  currentBlock :: Label,
  phiInfo :: Map.Map Operand PhiStruct,
  blockInfo :: Map.Map Label BlockStruct,
  currentDef :: Map.Map (Ident, Label) Operand,
  incompletePhis :: Map.Map Label [(Ident, Operand)]
  }

newState :: GenState
newState =
  GenState {labelCounter = 0, regCounter = 0,
  stackOffset = 0, phiCounter=0, currentBlock = Label "",
  currentDef = Map.empty, phiInfo = Map.empty, blockInfo = Map.empty,
  incompletePhis = Map.empty}

newPhi :: Label -> GenM Operand
newPhi block = do
  state <- get
  let number = phiCounter state
  let op = Phi ("phi" ++ show number)
  let phistruct = PhiStruct {operands = [], block = block}
  let newInfo = Map.insert op phistruct $ phiInfo state
  put state{phiCounter = number+1, phiInfo=newInfo}
  return op

getPhiInfo :: Operand -> GenM PhiStruct
getPhiInfo phi = do
  state <- get
  case Map.lookup phi $ phiInfo state of
    Just x -> return x
    Nothing -> fail "internal error in ssa construction"

insertPhiInfo :: Operand -> PhiStruct -> GenM ()
insertPhiInfo phi phistruct =
  modify $ \s -> s {phiInfo = Map.insert phi phistruct $ phiInfo s}

getBlockInfo :: Label -> GenM BlockStruct
getBlockInfo label = do
  state <- get
  case Map.lookup label $ blockInfo state of
    Just x -> return x
    Nothing -> fail "internal error in ssa construction"

insertBlockInfo :: Label -> BlockStruct -> GenM ()
insertBlockInfo block blockstruct =
  modify $ \s -> s {blockInfo = Map.insert block blockstruct $ blockInfo s}

enterBlock :: Label -> GenM ()
enterBlock l = do
  modify (\s -> s{currentBlock = l,
    blockInfo = Map.insert l newBlockStruct $ blockInfo s})
  emit $ QLabel l

getIncompletePhis :: Label -> GenM [(Ident, Operand)]
getIncompletePhis block = do
  s <- get
  return $ Map.findWithDefault [] block (incompletePhis s)

insertIncompletePhi :: Label -> Ident -> Operand -> GenM ()
insertIncompletePhi block variable value = do
  list <- getIncompletePhis block
  let newlist = (variable, value):list
  modify (\s -> s {incompletePhis = Map.insert block newlist $ incompletePhis s})

appendOperand :: Operand -> Operand -> GenM ()
appendOperand phi op = do
  phistruct <- getPhiInfo phi
  insertPhiInfo phi $ phistruct{operands = op:operands phistruct}

getPhiUsers :: Operand -> GenM [Operand]
getPhiUsers phi = do
  state <- get
  let flt phistruct = elem phi $ operands phistruct
  return $ filter (phi /=) (Map.keys $ Map.filter flt (phiInfo state))

replacePhiUses :: Operand -> Operand -> GenM ()
replacePhiUses phi new = do
  let {rmstr phistruct =
    phistruct {operands = new : filter (\x -> x /= phi && x /= new) (operands phistruct)}}
  modify (\s -> s{phiInfo = Map.delete phi . Map.map rmstr . phiInfo $ s  })

----------------------------------------------------
writeVariable :: Ident -> Label -> Operand -> GenM ()
writeVariable variable block value =
  modify (\s -> s{currentDef = Map.insert (variable, block) value $ currentDef s})

readVariable :: Ident -> Label -> GenM Operand
readVariable variable block = do
  state <- get
  case Map.lookup (variable, block) (currentDef state) of
    Just x -> return x
    Nothing -> readVariableRecursive variable block

readVariableRecursive :: Ident -> Label -> GenM Operand
readVariableRecursive variable block = do
  state <- get
  blockstruct <- getBlockInfo block
  let {gn
    | not . isSealed $ blockstruct =
      do val <- newPhi block
         insertIncompletePhi block variable val
         return val
    | 1 == (length . preds $ blockstruct) =
      readVariable variable $ head (preds blockstruct)
    | otherwise =
      do val <- newPhi block
         writeVariable variable block val
         addPhiOperands variable val}
  val <- gn
  writeVariable variable block val
  return val

addPhiOperands :: Ident -> Operand -> GenM Operand
addPhiOperands variable phi = do
  phistruct <- getPhiInfo phi
  blockstruct <- getBlockInfo $ block phistruct
  let {appOp block = do
    val <- readVariable variable block
    appendOperand phi val}
  mapM_ appOp $ preds blockstruct
  tryRemoveTrivialPhi phi

tryRemoveTrivialPhi :: Operand -> GenM Operand
tryRemoveTrivialPhi phi = do
  phistruct <- getPhiInfo phi
  let ops = filter (phi /=) $ operands phistruct
  if ops /= [] && any (head ops /=) ops then
    insertPhiInfo phi phistruct{operands=ops} >> return phi
  else do
    insertPhiInfo phi phistruct{operands=ops}
    let {same = if null . operands $ phistruct then Undef
      else head . operands $phistruct}
    users <- getPhiUsers phi
    replacePhiUses phi same
    mapM_ tryRemoveTrivialPhi users
    return same


sealBlock :: Label -> GenM ()
sealBlock block = do
  lst <- getIncompletePhis block
  mapM_ (uncurry addPhiOperands) lst
  blockstruct <- getBlockInfo block
  insertBlockInfo block $ blockstruct{isSealed = True}

--------------------------------------------------
---------------------------------------------------------------

emitQPhiPlaceholder :: Operand -> GenM Operand
emitQPhiPlaceholder phi = do
  dest <- newReg
  emit $ QPhiPlaceholder dest phi
  return dest

loadVar :: Ident -> GenM Operand
loadVar ident = do
  loc <- getVarLoc ident
  case loc of
    Stack -> do
      state <- get
      val <- readVariable ident $ currentBlock state
      case val of
        Undef -> fail "internal error during SSA construction (undef)"
        Reg _ -> return val
        Phi _ -> emitQPhiPlaceholder val

storeVar :: Ident -> Operand -> GenM ()
storeVar ident reg = do
  loc <- getVarLoc ident
  case loc of
    Stack -> do
      state <- get
      writeVariable ident (currentBlock state) reg

data GenEnv = GenEnv {
  varInfo :: Map.Map Ident (VarLoc, Type),
  basePointer :: Operand }

type GenM a = RWS GenEnv [Quadruple] GenState a


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
  r <- emitLitInt $ toInteger ((-4)*offset)
  dest <- emitBin QBinOp QSub base r
  emit $ QStore dest value


emitLitInt :: Integer -> GenM Operand
emitLitInt i = do
  dest <- newReg
  tell [QLitInt dest i]
  return dest

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
  EVar ident ->
    loadVar ident
  ELitInt integer -> emitLitInt integer
  ELitTrue -> emitLitInt 1
  ELitFalse -> emitLitInt 0
  EApp ident exprs -> do
    vs <- mapM genExpr exprs
    mapM_ emitParam vs
    emitCall ident
  EString string -> do
    r1 <- emitLitInt $ toInteger (length string + 1)
    r2 <- emitLitInt 4
    emitParam r1
    emitParam r2
    allocated <- emitCallExternal "calloc"
    values <- mapM (emitLitInt .toInteger. fromEnum) string
    sequence_ [emitWrite allocated (offset-1) value | (offset, value) <- zip [1..(length string)] values]
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
    enterBlock l1
    e2 <- genExpr expr2
    e3 <- emitAnd e1 e2
    emit $ QGoto l2
    enterBlock l2
    emitPhi e1 e2
  EOr expr1 expr2 -> do
    e1 <- genExpr expr1
    [l1, l2] <- replicateM 2 newLabel
    emit $ QGotoBool e1 l2 l1
    enterBlock l1
    e2 <- genExpr expr2
    e3 <- emitAnd e1 e2
    emit $ QGoto l2
    enterBlock l2
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
    e <- genExpr expr
    storeVar ident e
    ask
  Incr ident -> do
    val <- loadVar ident
    val <- emitUn QLoad reg
    inc <- emitLitInt 1
    res <- emitBin QBinOp QAdd val inc
    storeVar ident res
    ask
  Decr ident -> do
    val <- loadVar ident
    inc <- emitLitInt 1
    res <- emitBin QBinOp QSub val inc
    storeVar ident res
    ask
  Ret expr -> genExpr expr >>= (emit . QRet) >> ask
  VRet -> emit QVRet >> ask
  Cond expr stmt -> do
    [l1, l2] <- replicateM 2 newLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    enterBlock l1
    genStmt stmt
    emit $ QGoto l2
    enterBlock l2
    ask
  CondElse expr stmt1 stmt2 -> do
    [l1, l2, l3] <- replicateM 3 newLabel
    e <- genExpr expr
    emit $ QGotoBool e l1 l2
    enterBlock l1
    genStmt stmt1
    emit $ QGoto l3
    enterBlock l2
    genStmt stmt2
    emit $ QGoto l3
    enterBlock l3
    ask
  While expr stmt -> do
    [l1, l2] <- replicateM 2 newLabel
    e1 <- genExpr expr
    emit $ QGotoBool e1 l1 l2
    enterBlock l1
    genStmt stmt
    e2 <- genExpr expr
    emit $ QGotoBool e2 l1 l2
    enterBlock l2
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
        enterBlock (Label "entry")
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
