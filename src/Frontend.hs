module Frontend
  (getRepr, Err, Program, predefs, Type(..), transType)
    where

import qualified Data.Map as Map
import ErrM
import ParLatte
import PrintLatte
import AbsLatte hiding (Type(..))
import qualified AbsLatte (Type(..))
import Control.Monad
import Text.Printf

data Type
    = Int
    | Str
    | Bool
    | Void
    | Array (Type)
    | Fun (Type) [Type]
  deriving (Eq, Ord, Show)
instance Print (Type) where
  prt i e = case e of
    Int -> prPrec i 0 (concatD [doc (showString "int")])
    Str -> prPrec i 0 (concatD [doc (showString "string")])
    Bool -> prPrec i 0 (concatD [doc (showString "boolean")])
    Void -> prPrec i 0 (concatD [doc (showString "void")])
    Array type_ -> prPrec i 0 (concatD [prt 0 type_, doc (showString "[]")])
    Fun type_ types -> prPrec i 0 (concatD [prt 0 type_, doc (showString "("), prt 0 types, doc (showString ")")])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])

transType :: AbsLatte.Type a -> Type
transType x = case x of
  AbsLatte.Int _ -> Int
  AbsLatte.Str _ -> Str
  AbsLatte.Bool _ -> Bool
  AbsLatte.Void _ -> Void
  AbsLatte.Array _ type_ -> Array $ transType type_
  AbsLatte.Fun _ type_ types -> Fun (transType type_) (map transType types)

type LineInfo = Maybe (Int, Int)

data FunType = FunType (Type) [Type] deriving (Eq)

type VarContext = Map.Map Ident (Type, Bool)
type FunContext = Map.Map Ident FunType
type Env = (FunContext, [VarContext])


instance PrintfArg Ident where
  formatArg (Ident s) _ = showString s

errToBool :: Err a -> Bool
errToBool (Ok _) = True
errToBool (Bad _) = False


checkVarBlockDecl :: Env -> Ident -> Bool
checkVarBlockDecl (_, h:_) ident =
  case Map.lookup ident h of
    Just _ -> True
    Nothing -> False
getVarType :: Env -> Ident -> Err (Type, Bool)
getVarType (_, ctx) ident =
  fnd ctx where
    fnd l = case l of
      t:tt -> case Map.lookup ident t of
        Just x -> return x
        Nothing -> fnd tt
      [] -> fail $ printf "undeclared variable %s" ident
getFunType :: Env -> Ident -> Err FunType
getFunType (ctx, _) ident =
  case Map.lookup ident ctx of
    Just x -> return x
    Nothing -> fail $ printf "undeclared function %s" ident
updateVarType :: Env -> Ident -> (Type, Bool) -> Err Env
updateVarType (x, t:tt) ident typ =
  return (x, Map.insert ident typ t : tt)
updateFunType :: Env -> Ident -> FunType -> Err Env
updateFunType (x, ctx) ident typ =
  case Map.insertLookupWithKey f1 ident typ x of
    (Nothing, r) -> return (r, ctx)
    (Just _, _) -> fail $ printf "function %s redefined" ident
  where f1 _ _ a = a
enterBlock:: Env -> Env
enterBlock (x, ctx) = (x, Map.empty : ctx)
emptyEnv :: Env
emptyEnv = (Map.empty, [Map.empty])


concatErrors :: [Err a] -> Err ()
concatErrors x = case x of
  h:t -> case h of
    Ok _ -> concatErrors t
    Bad e -> case concatErrors t of
      Ok i -> Ok i
      Bad e2 -> Bad $ e ++ "\n" ++ e2
  [] -> Ok ()

checkExpr :: Env -> Type -> Expr a -> Err ()
checkExpr env typ expr = do
  typ2 <- inferExpr env expr
  unless (typ2 == typ) $
    fail $
      printf "type of %s : expected %s but found %s"
        (printTree expr)  (printTree typ)  (printTree typ2)

inferExpr :: Env -> Expr a -> Err Type
inferExpr env x = case x of
  EVar _ ident ->  fst <$> getVarType env ident
  ELitInt _ _ -> return Int
  ELitTrue _ -> return Bool
  ELitFalse _ -> return Bool
  EApp _ ident exprs -> do
    (FunType ret params) <- getFunType env ident
    unless (length params == length exprs) $
      fail $ printf
        "incorrect number of parameters in %s" (printTree x)
    zipWithM_ (checkExpr env) params exprs
    return ret
  EString _ _ -> return Str
  Neg _ expr -> checkExpr env Int expr >> return Int
  Not _ expr -> checkExpr env Bool expr >> return Bool
  EMul _ expr1 mulop expr2 ->
    checkTwo Int expr1 expr2 >> return Int
  EAdd _ expr1 addop expr2 -> case addop of
    Minus _ -> checkTwo Int expr1 expr2 >> return Int
    Plus _ -> do
      t1 <- inferExpr env expr1
      t2 <- inferExpr env expr2
      when (t1 /= t2 || t1 /= Str && t1 /= Int)
        (fail $ printf "invalid operands in %s" $ printTree x)
      return t1
  ERel _ expr1 relop expr2 ->
    case relop of
      EQU _ -> checkSame expr1 expr2 >> return Bool
      NE _ -> checkSame expr1 expr2 >> return Bool
      _ -> checkTwo Int expr1 expr2 >> return Bool
  EAnd _ expr1 expr2 ->
    checkTwo Bool expr1 expr2 >> return Bool
  EOr x expr1 expr2 -> inferExpr env (EAnd x expr1 expr2)
  where
    checkTwo type_ expr1 expr2 =
      checkExpr env type_ expr1 >> checkExpr env type_ expr2
    checkSame expr1 expr2 = do
      t1 <- inferExpr env expr1
      checkExpr env t1 expr2

checkStmts :: Env -> Type -> [Stmt a] -> Err Env
checkStmts env rettype =
  foldM (\env1 stmt -> checkStmt env1 rettype stmt) env

checkStmt :: Env -> Type -> Stmt a -> Err Env
checkStmt env rettype x = case x of
  Empty _-> return env
  BStmt _ (Block _ stmts) -> do
    checkStmts (enterBlock env) rettype stmts
    return env
  Decl _ type_ items -> foldM process env items
    where {process env1 item = case item of
      NoInit _ ident -> do
        when (checkVarBlockDecl env ident)
          (fail $ printf "variable %s redeclared in %s" ident $ printTree x)
        updateVarType env1 ident (transType type_, False)
      Init _ ident expr -> do
        when (checkVarBlockDecl env ident)
          (fail $ printf "variable %s redeclared in %s" ident $ printTree x)
        checkExpr env (transType type_) expr
        updateVarType env1 ident (transType type_, False)}
  Ass x ident expr -> do
    (type_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s" ident $
      printTree (Ass x ident expr))
    checkExpr env type_ expr
    return env
  Incr x ident -> do
    (_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s" ident $
      printTree (Incr x ident))
    checkExpr env Int (EVar x ident)
    return env
  Decr x ident -> do
    (_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s" ident $
      printTree (Incr x ident))
    checkExpr env Int (EVar x ident)
    return env
  Ret _ expr -> checkExpr env rettype expr >> return env
  VRet _ -> unless (rettype == Void) (fail "return value needed") >> return env
  Cond _ expr stmt -> do
    checkExpr env Bool expr
    checkStmt env rettype stmt
    return env
  CondElse _ expr stmt1 stmt2 -> do
    checkExpr env Bool expr
    checkStmt env rettype stmt1
    checkStmt env rettype stmt2
    return env
  While x expr stmt -> checkStmt env rettype (Cond x expr stmt)
  SExp _ expr -> inferExpr env expr >> return env


declTopDef :: Env -> TopDef a -> Err Env
declTopDef env (FnDef _ type_ ident args block) =
  updateFunType env ident (FunType (transType type_) argtypes)
  where argtypes = map (\(Arg _ type1 _)-> transType type1) args

checkTopDef :: Env -> TopDef a -> Err ()
checkTopDef env (FnDef _ type_ ident args block)  = do
  let {insertArg env1 (Arg _ type1 ident1) = do
    when (checkVarBlockDecl env1 ident1)
      (fail $ printf "parameter %s redeclared in function definition for %s" ident1 ident)
    updateVarType env1 ident1 (transType type1, True)}
  env2 <- foldM insertArg env args
  let (Block _ stmts) = block
  void $ checkStmts env2 (transType type_) stmts
  unless (transType type_ == Void || checkReturnsBlock block) $
    fail $ printf "function %s must return a value" ident


checkReturnsBlock :: Block a -> Bool
checkReturnsBlock (Block _ stmts) =
  any checkReturnsStmt stmts

checkReturnsStmt :: Stmt a -> Bool
checkReturnsStmt x = case x of
  Empty _ -> False
  BStmt _ block -> checkReturnsBlock block
  Decl _ type_ items -> False
  Ass _ ident expr -> False
  Incr _ ident -> False
  Decr _ ident -> False
  Ret _ expr -> True
  VRet _ -> True
  Cond _ expr stmt -> case expr of
    ELitTrue _ -> checkReturnsStmt stmt
    _ -> False
  CondElse _ expr stmt1 stmt2 -> case expr of
    ELitTrue _ -> checkReturnsStmt stmt1
    ELitFalse _ -> checkReturnsStmt stmt2
    _ -> checkReturnsStmt stmt1 && checkReturnsStmt stmt2
  While _ expr stmt -> case expr of
    ELitTrue _ -> checkReturnsStmt stmt
    _ -> False
  SExp _ expr -> False

predefs :: [TopDef LineInfo]
predefs = [
  FnDef Nothing (AbsLatte.Void Nothing) (Ident "printInt") [Arg Nothing (AbsLatte.Int Nothing) $ Ident ""] $ Block Nothing [],
  FnDef Nothing (AbsLatte.Void Nothing) (Ident "printString") [Arg Nothing (AbsLatte.Str Nothing) $ Ident ""] $ Block Nothing [],
  FnDef Nothing (AbsLatte.Void Nothing) (Ident "error") [] $ Block Nothing [],
  FnDef Nothing (AbsLatte.Int Nothing) (Ident "readInt") [] $ Block Nothing [],
  FnDef Nothing (AbsLatte.Str Nothing) (Ident "readString") [] $ Block Nothing []]

checkProgram :: Program LineInfo -> Err (Program LineInfo)
checkProgram (Program i topdefs) = do
  env1 <- foldM declTopDef emptyEnv (predefs ++ topdefs)
  let checked = map (checkTopDef env1) topdefs
  if any (not . errToBool) checked then
    let {append a x = case x of
      Ok _ -> a
      Bad e -> a ++ e ++ "\n"}
    in fail $ foldl append "" checked
  else do
    mainType <- getFunType env1 (Ident "main")
    when (mainType /= FunType Int [])
      (fail  "main function has wrong type (should be int())")
    return $ Program i topdefs


parse :: String -> Err (Program LineInfo)
parse = pProgram . myLexer

getRepr:: String -> Either String (Program LineInfo)
getRepr s =
  case parse s >>= checkProgram of
    Bad e -> Left e
    Ok p -> Right p
