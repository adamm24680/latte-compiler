module Frontend
  (getRepr, Err, Program, predefs)
    where

import qualified Data.Map as Map
import ErrM
import ParLatte
import PrintLatte
import AbsLatte
import Control.Monad
import Text.Printf

data FunType = FunType Type [Type] deriving (Eq)

type VarContext = Map.Map Ident (Type, Bool)
type FunContext = Map.Map Ident FunType
type Env = (FunContext, [VarContext])


instance PrintfArg Ident where
  formatArg (Ident s) _ = showString s

errToBool :: Err a -> Bool
errToBool (Ok _) = True
errToBool (Bad _) = False


checkVarBlockDecl :: Env -> Ident -> Bool
checkVarBlockDecl (_, h:t) ident =
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

checkExpr :: Env -> Type -> Expr -> Err ()
checkExpr env typ expr = do
  typ2 <- inferExpr env expr
  unless (typ2 == typ) $
    fail $
      printf "type of %s : expected %s but found %s"
        (printTree expr)  (printTree typ)  (printTree typ2)

inferExpr :: Env -> Expr -> Err Type
inferExpr env x = case x of
  EVar ident ->  fst <$> getVarType env ident
  ELitInt integer -> return Int
  ELitTrue -> return Bool
  ELitFalse -> return Bool
  EApp ident exprs -> do
    (FunType ret params) <- getFunType env ident
    unless (length params == length exprs) $
      fail $ printf
        "incorrect number of parameters in %s" (printTree x)
    zipWithM_ (checkExpr env) params exprs
    return ret
  EString string -> return Str
  Neg expr -> checkExpr env Int expr >> return Int
  Not expr -> checkExpr env Bool expr >> return Bool
  EMul expr1 mulop expr2 ->
    checkTwo Int expr1 expr2 >> return Int
  EAdd expr1 addop expr2 -> case addop of
    Minus -> checkTwo Int expr1 expr2 >> return Int
    Plus -> do
      t1 <- inferExpr env expr1
      t2 <- inferExpr env expr2
      when (t1 /= t2 || t1 /= Str && t1 /= Int)
        (fail $ printf "invalid operands in %s" $ printTree x)
      return t1
  ERel expr1 relop expr2 ->
    case relop of
      EQU -> checkSame expr1 expr2 >> return Bool
      NE -> checkSame expr1 expr2 >> return Bool
      _ -> checkTwo Int expr1 expr2 >> return Bool
  EAnd expr1 expr2 ->
    checkTwo Bool expr1 expr2 >> return Bool
  EOr expr1 expr2 -> inferExpr env (EAnd expr1 expr2)
  where
    checkTwo type_ expr1 expr2 =
      checkExpr env type_ expr1 >> checkExpr env type_ expr2
    checkSame expr1 expr2 = do
      t1 <- inferExpr env expr1
      checkExpr env t1 expr2

checkStmts :: Env -> Type -> [Stmt] -> Err Env
checkStmts env rettype =
  foldM (\env1 stmt -> checkStmt env1 rettype stmt) env

checkStmt :: Env -> Type -> Stmt -> Err Env
checkStmt env rettype x = case x of
  Empty -> return env
  BStmt (Block stmts) -> do
    checkStmts (enterBlock env) rettype stmts
    return env
  Decl type_ items -> foldM process env items
    where {process env1 item = case item of
      NoInit ident -> do
        when (checkVarBlockDecl env ident)
          (fail $ printf "variable %s redeclared in %s" ident $ printTree x)
        updateVarType env1 ident (type_, False)
      Init ident expr -> do
        when (checkVarBlockDecl env ident)
          (fail $ printf "variable %s redeclared in %s" ident $ printTree x)
        checkExpr env type_ expr
        updateVarType env1 ident (type_, False)}
  Ass ident expr -> do
    (type_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s" ident $
      printTree (Ass ident expr))
    checkExpr env type_ expr
    return env
  Incr ident -> do
    (_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s" ident $
      printTree (Incr ident))
    checkExpr env Int (EVar ident)
    return env
  Decr ident -> do
    (_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s" ident $
      printTree (Incr ident))
    checkExpr env Int (EVar ident)
    return env
  Ret expr -> checkExpr env rettype expr >> return env
  VRet -> unless (rettype == Void) (fail "return value needed") >> return env
  Cond expr stmt -> do
    checkExpr env Bool expr
    checkStmt env rettype stmt
    return env
  CondElse expr stmt1 stmt2 -> do
    checkExpr env Bool expr
    checkStmt env rettype stmt1
    checkStmt env rettype stmt2
    return env
  While expr stmt -> checkStmt env rettype (Cond expr stmt)
  SExp expr -> inferExpr env expr >> return env


declTopDef :: Env -> TopDef -> Err Env
declTopDef env (FnDef type_ ident args block) =
  updateFunType env ident (FunType type_ argtypes)
  where argtypes = map (\(Arg type1 _)-> type1) args

checkTopDef :: Env -> TopDef -> Err ()
checkTopDef env (FnDef type_ ident args block)  = do
  let {insertArg env1 (Arg type1 ident1) = do
    when (checkVarBlockDecl env1 ident1)
      (fail $ printf "parameter %s redeclared in function definition for %s" ident1 ident)
    updateVarType env1 ident1 (type1, True)}
  env2 <- foldM insertArg env args
  let (Block stmts) = block
  void $ checkStmts env2 type_ stmts
  unless (checkReturnsBlock block) $
    fail $ printf "function %s must return a value" ident


checkReturnsBlock :: Block -> Bool
checkReturnsBlock (Block stmts) =
  any checkReturnsStmt stmts

checkReturnsStmt :: Stmt -> Bool
checkReturnsStmt x = case x of
  Empty -> False
  BStmt block -> checkReturnsBlock block
  Decl type_ items -> False
  Ass ident expr -> False
  Incr ident -> False
  Decr ident -> False
  Ret expr -> True
  VRet -> True
  Cond expr stmt -> case expr of
    ELitTrue -> True
    _ -> checkReturnsStmt stmt
  CondElse expr stmt1 stmt2 -> case expr of
    ELitTrue -> checkReturnsStmt stmt1
    ELitFalse -> checkReturnsStmt stmt2
    _ -> checkReturnsStmt stmt1 && checkReturnsStmt stmt2
  While expr stmt -> case expr of
    ELitTrue -> checkReturnsStmt stmt
    _ -> False
  SExp expr -> False

predefs :: [TopDef]
predefs = [FnDef Void (Ident "printInt") [Arg Int $ Ident ""] $ Block [],
  FnDef Void (Ident "printString") [Arg Str $ Ident ""] $ Block [],
  FnDef Void (Ident "error") [] $ Block [],
  FnDef Int (Ident "readInt") [] $ Block [],
  FnDef Str (Ident "readString") [] $ Block []]

checkProgram :: Program -> Err Program
checkProgram (Program topdefs) = do
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
    return $ Program topdefs


parse :: String -> Err Program
parse = pProgram . myLexer

getRepr:: String -> Either String Program
getRepr s =
  case parse s >>= checkProgram of
    Bad e -> Left e
    Ok p -> Right p
