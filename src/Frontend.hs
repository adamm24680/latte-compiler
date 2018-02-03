module Frontend
  (getRepr, Err, predefs,
  VType, voidType, intType, stringType, boolType,
  FunSig(..), makeFunSig, Program)
    where

import           AbsLatte
import           Control.Monad
import           Control.Monad.Reader
import           Data.List
import qualified Data.Map.Strict           as Map
import           Data.Maybe
import qualified ErrM
import           Generics.Deriving.Copoint (GCopoint, gcopoint)
import           ParLatte                  (myLexer, pProgram)
import           PrintLatte


instance GCopoint []
instance GCopoint RelOp
instance GCopoint MulOp
instance GCopoint AddOp
instance GCopoint Expr
instance GCopoint Item
instance GCopoint Type
instance GCopoint Block
instance GCopoint Stmt
instance GCopoint Arg
instance GCopoint ClassEl
instance GCopoint ClassExt
instance GCopoint TopDef
instance GCopoint Program

newtype LineData = LineData (Maybe (Int, Int))
instance Show LineData where
  show (LineData(Just (l, c))) = ", line " ++ show l ++ " column " ++ show c
  show (LineData Nothing)      = ""

--data TreeInfo = TreeInfo {lineData :: LineData, exprType :: VType}
type Err = Either String
type VType = Type ()
data FunSig = FunSig VType [VType] deriving (Eq)
data ClassSig = ClassSig { super     :: Maybe ClassSig,
                           fields    :: [(Ident, VType)],
                           methods   :: [(Ident, FunSig)],
                           overrides :: [Ident] }
data GlobalEnv = GlobalEnv [(Ident, ClassSig)] [(Ident, FunSig)]
data FrontendEnv = FrontendEnv { globalEnv  :: GlobalEnv,
                                 lineData   :: LineData,
                                 returnType :: VType,
                                 inClass    :: Maybe ClassSig }
type FrontendM = ReaderT FrontendEnv Err
type VarContext = Map.Map Ident VType
type VarEnv = [VarContext]

makeFunSig :: Type a -> [Arg b] -> FunSig
makeFunSig type_ args =
  FunSig (void type_) $ map (\(Arg _ argtype _) -> void argtype) args

checkParamRedeclaration :: Show a => [Arg a] -> Err ()
checkParamRedeclaration =
  let {foldf acc (Arg li _ ident) =
    if ident `elem` acc then
       Left $ "parameter " ++ show ident ++ "redeclared" ++ show li
    else
      return $ ident : acc } in
  foldM_ foldf []

voidType :: VType
voidType = Void ()

intType = Int ()
stringType = Str ()
boolType = Bool ()

fmapVoidType :: Functor a => a b -> a VType
fmapVoidType = fmap (const voidType)

extractClassName :: Type a -> Maybe Ident
extractClassName (Class _ ident) = Just ident
extractClassName _ = Nothing

processTopDef :: Show a => GlobalEnv -> TopDef a -> Err GlobalEnv
processTopDef (GlobalEnv cl fl) (FnDef li type_ ident args _) = do
  when (isJust $ lookup ident fl) $
    Left $ "global function " ++ show ident ++ "redeclared" ++ show li
  checkParamRedeclaration args
  return $ GlobalEnv cl ((ident, funSig) : fl)
  where
    funSig = makeFunSig type_ args
processTopDef (GlobalEnv cl fl) (ClassDef li ident classext classels) = do
  when (isJust $ lookup ident cl) $
    Left ("class " ++ show ident ++ "redeclared" ++ show li )
  super <- superClass
  declMethods <- foldM processMethodSignature [] classels
  declFields <- foldM processFieldDecl [] classels
  (newMethods, overrides) <- splitMethods declMethods
  let class_ = ClassSig {super = super,
                        fields = declFields,
                        methods = newMethods,
                        overrides = overrides}
  return $ GlobalEnv ((ident, class_) : cl) fl
  where
    superClass = case classext of
      Extends exli exident ->
        case lookup exident cl of
          Nothing -> Left ("unknown superclass " ++ show exident ++
            " in declaration of " ++ show ident ++ show exli)
          Just x -> return $ Just x
      NoExtend _ -> return Nothing
    splitMethods :: [(Ident, FunSig)] -> Err ([(Ident, FunSig)], [Ident])
    splitMethods l = do
      super1 <- superClass
      let partF (ident, _) = isNothing $ findInSuper methods super1 ident
      let (methods, overrides) = partition partF l
      return (methods, map fst overrides)
    processMethodSignature :: Show a => [(Ident, FunSig)] -> ClassEl a ->
      Err [(Ident, FunSig)]
    processMethodSignature ml (MethodDef li type_ ident args _) = do
      let sig = makeFunSig type_ args
      when (isJust $ lookup ident fl) $
        Left $ "global function " ++ show ident ++ "redeclared" ++ show li
      when (isJust $ lookup ident ml) $
        Left $ "class method " ++ show ident ++ "redeclared" ++ show li
      super1 <- superClass
      when (fromMaybe sig (findInSuper methods super1 ident) /= sig) $
        Left $ "invalid superclass method override in " ++ show ident ++ show li
      checkParamRedeclaration args
      Right $ (ident, sig) : ml
    processMethodSignature x _ = return x
    processFieldDecl :: Show a => [(Ident, VType)] -> ClassEl a ->
      Err [(Ident, VType)]
    processFieldDecl fieldl (FieldDef li type_ idents) = do
      let {checkFieldRedeclaration ident = do
        when (isJust $ lookup ident fieldl) $
          Left ("class field " ++ show ident ++ " redeclared" ++ show li)
        super1 <- superClass
        when (isJust $ findInSuper fields super1 ident) $
          Left ("superclass field " ++ show ident ++ " redeclared" ++ show li)
        }
      forM_ idents checkFieldRedeclaration
      return $ fieldl ++ map (\i -> (i, void type_)) idents
    processFieldDecl x _ = return x

findInSuper :: (ClassSig -> [(Ident, a)]) ->
  Maybe ClassSig -> Ident -> Maybe a
findInSuper accessor superclass ident = do
  superSig <- superclass
  case lookup ident $ accessor superSig of
    Just x  -> Just x
    Nothing -> findInSuper accessor (super superSig) ident

findClass :: GlobalEnv -> Ident -> Maybe ClassSig
findClass (GlobalEnv cl _) ident = lookup ident cl

checkReturnsStmt :: Stmt a -> Bool
checkReturnsStmt x = case x of
  BStmt _ (Block _ stmts) ->
    any checkReturnsStmt stmts
  Ret {} -> True
  VRet _ -> True
  Cond _ expr stmt -> case expr of
    ELitTrue _ -> checkReturnsStmt stmt
    _          -> False
  CondElse _ expr stmt1 stmt2 -> case expr of
    ELitTrue _  -> checkReturnsStmt stmt1
    ELitFalse _ -> checkReturnsStmt stmt2
    _           -> checkReturnsStmt stmt1 && checkReturnsStmt stmt2
  While _ expr stmt -> case expr of
    ELitTrue _ -> checkReturnsStmt stmt
    _          -> False
  _ -> False

raiseError :: String -> FrontendM a
raiseError estr = do
  li <- lineData <$> ask
  lift $ Left (estr ++ show li)

checkTypes :: VType -> [VType] -> FrontendM ()
checkTypes type_ types =
  unless (type_ `elem` types) $ raiseError $
    "type mismatch: " ++ printTree type_ ++ ", expected " ++ printTree types

findLocal :: VarEnv -> Ident -> Maybe VType
findLocal (h:t) ident =
  case Map.lookup ident h of
    Just type_ -> Just type_
    Nothing    -> findLocal t ident
findLocal [] _ = Nothing

findClassEl :: Ident -> (ClassSig -> [(Ident, a)]) -> ClassSig -> Maybe a
findClassEl ident accessor classSig =
  let index = accessor classSig in
  case lookup ident index of
    Just x -> Just x
    Nothing -> findInSuper accessor (super classSig) ident

findClassAndEl :: GlobalEnv -> Ident -> (ClassSig -> [(Ident, a)]) ->
   Ident -> Maybe a
findClassAndEl env ident accessor classIdent = do
  classSig <- findClass env classIdent
  let index = accessor classSig
  lookup ident index

findVar :: VarEnv -> Ident -> FrontendM (VType, Bool)
findVar env ident =
  case findLocal env ident of
    Just type_ -> return (type_, False)
    Nothing    -> do
      classSig <- inClass <$> ask
      case classSig >>= findClassEl ident fields of
        Just type_ -> return (type_, True)
        Nothing -> raiseError $ "variable " ++ show ident ++ " not found"

findFun :: Ident -> FrontendM (FunSig, Bool)
findFun ident = do
  GlobalEnv _ globalFuns <- globalEnv <$> ask
  case lookup ident globalFuns of
    Just funSig -> return (funSig, False)
    Nothing -> do
      classSig <- inClass <$> ask
      case classSig >>= findClassEl ident methods of
        Just sig -> return (sig, True)
        Nothing -> raiseError $ "procedure " ++ show ident ++ " not found"

findAndAnnotate :: VarEnv -> Expr LineData -> Ident ->
  (ClassSig -> [(Ident, a)]) -> FrontendM (Expr VType, a)
findAndAnnotate env expr ident accessor = do
  newExpr <- annotateExpr env expr
  genv <- globalEnv <$> ask
  result <-
    case extractClassName (gcopoint newExpr) >>= findClassAndEl genv ident accessor of
      Just type_ -> return type_
      Nothing -> raiseError $
        printTree expr ++ " does not have an element called " ++ show ident
  return (newExpr, result)

annotateAndCheckArgs :: VarEnv -> Ident -> [Expr LineData] -> [VType] ->
  FrontendM [Expr VType]
annotateAndCheckArgs env ident exprs argtypes = do
  newExprs <- forM exprs $ annotateExpr env
  when (length exprs /= length argtypes) $ raiseError $
    "incorrect number of parameter to function "++ show ident ++
    ", expected " ++ show (length argtypes) ++ " got " ++ show (length exprs)
  zipWithM_ (\x y -> checkTypes (gcopoint x) [y]) newExprs argtypes
  return newExprs

annotateExpr :: VarEnv -> Expr LineData -> FrontendM (Expr VType)
annotateExpr env expression =
  local (\fenv -> fenv {lineData = gcopoint expression}) comp
  where
    comp = case expression of
      ENull _ _-> undefined -- TODO
      EVar _ ident -> do
        (type_, inClass) <- findVar env ident
        if inClass then
          return $ EField type_ (EThis voidType) ident
        else
          return $ EVar type_ ident
      ELitInt _ integer -> return $ ELitInt intType integer
      ELitTrue _ -> return $ ELitTrue boolType
      ELitFalse _ -> return $ ELitFalse boolType
      ENew _ type_ -> return $ ENew (void type_) (fmapVoidType type_)
      EApp _ ident exprs -> do
        (FunSig rtype argtypes, inClass) <- findFun ident
        newExprs <- annotateAndCheckArgs env ident exprs argtypes
        if inClass then
          return $ EMethod rtype (EThis voidType) ident newExprs
        else
          return $ EApp rtype ident newExprs
      EString _ string -> return $ EString stringType string -- TODO sanitization?
      EField _ expr ident -> do
        (newExpr, type_) <- findAndAnnotate env expr ident fields
        return $ EField type_ newExpr ident
      EMethod _ expr ident exprs -> do
        (newExpr, FunSig rtype argtypes) <- findAndAnnotate env expr ident methods
        newExprs <- annotateAndCheckArgs env ident exprs argtypes
        return $ EMethod rtype newExpr ident newExprs
      Neg _ expr -> do
        newExpr <- annotateExpr env expr
        checkTypes (gcopoint newExpr) [intType]
        return $ Neg intType newExpr
      Not _ expr -> do
        newExpr <- annotateExpr env expr
        checkTypes (gcopoint newExpr) [boolType]
        return $ Not boolType newExpr
      EMul _ expr1 mulop expr2 -> do
        newExpr1 <- annotateExpr env expr1
        checkTypes (gcopoint newExpr1) [intType]
        newExpr2 <- annotateExpr env expr2
        checkTypes (gcopoint newExpr2) [intType]
        return $ EMul intType newExpr1 (fmapVoidType mulop) newExpr2
      EAdd _ expr1 addop expr2 -> do
        newExpr1 <- annotateExpr env expr1
        let type_ = gcopoint newExpr1
        checkTypes type_ expectedTypes
        newExpr2 <- annotateExpr env expr2
        checkTypes (gcopoint newExpr2) [type_]
        return $ EAdd type_ newExpr1 (fmapVoidType addop) newExpr2
        where
          expectedTypes = case addop of
            Plus _  -> [intType, stringType]
            Minus _ -> [intType]
      ERel _ expr1 relop expr2 -> do
        newExpr1 <- annotateExpr env expr1
        let type_ = gcopoint newExpr1
        checkTypes type_ expectedTypes
        newExpr2 <- annotateExpr env expr2
        checkTypes (gcopoint newExpr2) [type_]
        return $ ERel boolType newExpr1 (fmapVoidType relop) newExpr2
        where
          expectedTypes = case relop of
            EQU _ -> [stringType, intType, boolType]
            NE _  -> [stringType, intType, boolType]
            _     -> [intType]
      EAnd _ expr1 expr2 -> do
        (newExpr1, newExpr2) <- checkBoolTypes expr1 expr2
        return $ EAnd boolType newExpr1 newExpr2
      EOr _ expr1 expr2 -> do
        (newExpr1, newExpr2) <- checkBoolTypes expr1 expr2
        return $ EOr boolType newExpr1 newExpr2
      EThis _ -> error "'this.' should be internal"
      where
        checkBoolTypes expr1 expr2 = do
          newExpr1 <- annotateExpr env expr1
          checkTypes (gcopoint newExpr1) [boolType]
          newExpr2 <- annotateExpr env expr2
          checkTypes (gcopoint newExpr2) [boolType]
          return (newExpr1, newExpr2)

annotateBlockVar :: VType -> (VarEnv, [Item VType]) -> Item LineData ->
  FrontendM (VarEnv, [Item VType])
annotateBlockVar type_ (env@(currentEnv : rest), acc) item =
  case item of
    NoInit li ident -> local (\fenv -> fenv{lineData = li}) $ do
      newEnv <- insertDeclaration ident type_
      return (newEnv : rest, NoInit voidType ident : acc)
    Init li ident expr -> local (\fenv -> fenv{lineData = li}) $ do
      annExpr <- annotateExpr env expr
      checkTypes (gcopoint annExpr) [type_]
      newEnv <- insertDeclaration ident type_
      return (newEnv : rest, Init voidType ident annExpr : acc)
  where
    insertDeclaration :: Ident -> VType -> FrontendM VarContext
    insertDeclaration ident type_ = do
      li <- lineData <$> ask
      when (ident `Map.member` currentEnv)
        (lift $ Left $ "block variable " ++ show ident ++ "redeclared" ++ show li)
      return $ Map.insert ident (void type_) currentEnv
annotateBlockVar _ _ _ = error "empty item list (should not parse)"

annotateStmt :: VarEnv -> Stmt LineData ->
  FrontendM (VarEnv, Stmt VType)
annotateStmt env stmt =
  local (\fenv -> fenv {lineData = gcopoint stmt}) comp
  where
    comp = case stmt of
      Empty _ -> return (env, Empty voidType)
      BStmt _ block -> do
        annBlock <- annotateBlock env block
        return (env, BStmt voidType annBlock)
      Decl _ type_ items -> do
        let foldf = annotateBlockVar $ void type_
        (newEnv, rres) <- foldM foldf (env, []) items
        let result = reverse rres
        return (newEnv, Decl voidType (fmapVoidType type_) result)
      Ass _ ident expr -> do
        (type_, inClass) <- findVar env ident
        newExpr <- annotateExpr env expr
        checkTypes (gcopoint newExpr) [type_]
        if inClass then
          return (env, AssField voidType eThis ident newExpr)
        else
          return (env, Ass voidType ident newExpr)
      AssField _ expr1 ident expr2 -> undefined -- TODO
      Incr _ ident -> do
        (type_, inClass) <- findVar env ident
        checkTypes type_ [intType]
        if inClass then
          return (env, IncrField voidType eThis ident)
        else
          return (env, Incr voidType ident)
      IncrField _ expr ident -> undefined -- TODO
      Decr _ ident -> do
        (type_, inClass) <- findVar env ident
        checkTypes type_ [intType]
        if inClass then
          return (env, IncrField voidType eThis ident)
        else
          return (env, Decr voidType ident)
      DecrField _ expr ident -> undefined -- TODO
      Ret _ expr -> do
        rtype <- returnType <$> ask
        newExpr <- annotateExpr env expr
        checkTypes (gcopoint newExpr) [rtype]
        return (env, Ret voidType newExpr)
      VRet _ -> do
        rtype <- returnType <$> ask
        unless (rtype == Void ()) $ raiseError
          "function with return type void cannot return a value"
        return (env, fmapVoidType stmt)
      Cond _ expr stmt -> do
        newExpr <- annotateExpr env expr
        checkTypes (gcopoint newExpr) [boolType]
        (_, newStmt) <- annotateStmt env stmt
        return (env, Cond voidType newExpr newStmt)
      CondElse _ expr stmt1 stmt2 -> do
        newExpr <- annotateExpr env expr
        checkTypes (gcopoint newExpr) [boolType]
        (_, newStmt1) <- annotateStmt env stmt1
        (_, newStmt2) <- annotateStmt env stmt2
        return (env, CondElse voidType newExpr newStmt1 newStmt2)
      While _ expr stmt -> do
        newExpr <- annotateExpr env expr
        checkTypes (gcopoint newExpr) [boolType]
        (_, newStmt) <- annotateStmt env stmt
        return (env, While voidType newExpr newStmt)
      SExp _ expr -> do
        newExpr <- annotateExpr env expr
        return (env, SExp voidType newExpr)
      where
        eThis = (EThis voidType)


annotateBlock :: VarEnv -> Block LineData  -> FrontendM (Block VType)
annotateBlock env (Block _ stmts) = do
  let newEnv = Map.empty : env
  let {foldf (env, res) stmt = do
    (env2, annStmt) <- annotateStmt env stmt
    return (env2, annStmt : res)}
  (_, res) <- foldM foldf (newEnv, []) stmts
  return $ Block voidType (reverse res)

annotateFun ::  ([Arg LineData], Block LineData ) ->
  FrontendM ([Arg VType], Block VType)
annotateFun (args, block) = do
  let {insertArg acc (Arg _ type_ ident) =
    Map.insert ident (void type_) acc }
  let initialEnv = foldl insertArg Map.empty args
  newBlock <- annotateBlock [initialEnv] block
  rettype <- returnType <$> ask
  unless (rettype == Void () || checkReturnsStmt (BStmt voidType newBlock)) $
    raiseError "function must return a value"
  let args2 = map fmapVoidType args
  return (args2, newBlock)


annotateTopDef :: GlobalEnv -> TopDef LineData -> Err (TopDef VType)
annotateTopDef globalEnv topDef =
  case topDef of
    (FnDef li rettype ident args block) -> do
      let rettype2 = fmapVoidType rettype
      let env = FrontendEnv {lineData = li,
                            globalEnv= globalEnv,
                            returnType = void rettype,
                            inClass = Nothing}
      (args2, block2) <- runReaderT (annotateFun (args, block)) env
      return $ FnDef voidType rettype2 ident args2 block2
    (ClassDef _ cident ext classEls) -> do
      newClassEls <- mapM annotateClassEl classEls
      let ext2 = fmapVoidType ext
      return $ ClassDef voidType cident ext2 newClassEls
      where
        annotateClassEl el = case el of
          MethodDef li rettype ident args block -> do
            let rettype2 = fmapVoidType rettype
            let env = FrontendEnv {lineData = li,
                                  globalEnv = globalEnv,
                                  returnType = void rettype,
                                  inClass = findClass globalEnv cident}
            (args2, block2) <- runReaderT (annotateFun (args, block)) env
            return $ MethodDef voidType rettype2 ident args2 block2
          _ -> return $ fmapVoidType el

checkMain :: GlobalEnv -> Err ()
checkMain (GlobalEnv _ fl) = do
  (FunSig rtype argtypes) <- case lookup (Ident "main") fl of
    Just x -> return x
    Nothing -> Left "main function not found"
  unless (rtype == intType) $
    Left "main should return int"
  unless (null argtypes) $
    Left "main should not accept any arguments"


annotateTree :: Program LineData -> Err (Program VType)
annotateTree (Program _ topdefs) = do
  _globalEnv <- foldM processTopDef (GlobalEnv [] []) (predefs' ++ topdefs)
  checkMain _globalEnv
  newTopdefs <- forM topdefs $ annotateTopDef _globalEnv
  return $ Program voidType newTopdefs

getRepr :: String -> Err (Program VType)
getRepr s =
  case pProgram $ myLexer s of
    ErrM.Bad e -> Left e
    ErrM.Ok p -> annotateTree $ fmap LineData p

predefs' :: [TopDef LineData]
predefs' = [
  FnDef emptyLineData (Void emptyLineData) (Ident "printInt") [Arg emptyLineData (Int emptyLineData) $ Ident ""] $ Block emptyLineData [],
  FnDef emptyLineData (Void emptyLineData) (Ident "printString") [Arg emptyLineData (Str emptyLineData) $ Ident ""] $ Block emptyLineData [],
  FnDef emptyLineData (Void emptyLineData) (Ident "error") [] $ Block emptyLineData [],
  FnDef emptyLineData (Int emptyLineData) (Ident "readInt") [] $ Block emptyLineData [],
  FnDef emptyLineData (Str emptyLineData) (Ident "readString") [] $ Block emptyLineData []]
  where
    emptyLineData = LineData Nothing

predefs :: [TopDef VType]
predefs = map fmapVoidType predefs'
