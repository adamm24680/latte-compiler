module Frontend
  --(getRepr, Err, Program, predefs, Type(..), transType)
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
data ClassSig = ClassSig {super :: Maybe ClassSig,
                    fields      :: [(Ident, VType)],
                    methods     :: [(Ident, FunSig)],
                    overrides   :: [Ident]}
data GlobalEnv = GlobalEnv [(Ident, ClassSig)] [(Ident, FunSig)]
data FrontendEnv = FrontendEnv { globalEnv :: GlobalEnv,
                                lineData   :: LineData,
                                returnType :: VType,
                                inClass    :: Maybe ClassSig }
type FrontendM = ReaderT FrontendEnv (Either String)
type VarContext = Map.Map Ident VType
type VarEnv = [VarContext]

makeFunSig :: Type a -> [Arg a] -> FunSig
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

generateSignatures :: Show a => Program a -> Err GlobalEnv
generateSignatures (Program _ defs) =
  foldM processTopDef (GlobalEnv [] []) defs

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
  Empty _ -> False
  BStmt _ (Block _ stmts) ->
    any checkReturnsStmt stmts
  Decl {} -> False
  Ass {} -> False
  Incr {} -> False
  Decr {} -> False
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
  SExp {} -> False

annotateExpr :: VarEnv -> Expr LineData -> FrontendM (Expr VType)
annotateExpr = undefined

annotateBlockVar :: VType -> (VarEnv, [Item VType]) -> Item LineData ->
  FrontendM (VarEnv, [Item VType])
annotateBlockVar type_ (env@(currentEnv : rest), acc) item =
  case item of
    NoInit li ident -> do
      newEnv <- insertDeclaration li ident type_
      return (newEnv : rest, NoInit voidType ident : acc)
    Init li ident expr -> do
      annExpr <- annotateExpr env expr
      newEnv <- insertDeclaration li ident type_
      return (newEnv : rest, Init voidType ident annExpr : acc)
  where
    insertDeclaration li ident type_ = do
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
        (newEnv, res) <- foldM foldf (env, []) items
        let type2 = fmap (const voidType) type_
        return (newEnv, Decl voidType type2 (reverse res))


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
  block2 <- annotateBlock [initialEnv] block
  let args2 = map (fmap (const voidType)) args
  return (args2, block2)


annotateTopDef :: GlobalEnv -> TopDef LineData -> Err (TopDef VType)
annotateTopDef globalEnv topDef =
  case topDef of
    (FnDef li rettype ident args block) -> do
      let rettype2 = fmap (const voidType) rettype
      let env = FrontendEnv {lineData = li,
                            globalEnv= globalEnv,
                            returnType = void rettype,
                            inClass = Nothing}
      (args2, block2) <- runReaderT (annotateFun (args, block)) env
      return $ FnDef voidType rettype2 ident args2 block2
    (ClassDef _ cident ext classEls) -> do
      newClassEls <- mapM annotateClassEl classEls
      let ext2 = fmap (const voidType) ext
      return $ ClassDef voidType cident ext2 newClassEls
      where
        annotateClassEl el = case el of
          MethodDef li rettype ident args block -> do
            let rettype2 = fmap (const voidType) rettype
            let env = FrontendEnv {lineData = li,
                                  globalEnv = globalEnv,
                                  returnType = void rettype,
                                  inClass = findClass globalEnv cident}
            (args2, block2) <- runReaderT (annotateFun (args, block)) env
            return $ MethodDef voidType rettype2 ident args2 block2
          _ -> return $ fmap (const voidType) el

annotateTree :: Program LineData -> Program VType
annotateTree (Program _ topdefs) = undefined topdefs
