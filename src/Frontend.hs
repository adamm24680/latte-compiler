module Frontend
  (getRepr, Err, Program)
    where

import qualified Data.Map as Map
import ErrM
import ParLatte
import PrintLatte
import AbsLatte
import Control.Monad

data FunType = FunType Type [Type] deriving (Eq)

type VarContext = Map.Map Ident Type
type FunContext = Map.Map Ident FunType
type Env = (FunContext, [VarContext])


errToBool :: Err a -> Bool
errToBool (Ok _) = True
errToBool (Bad _) = False


checkVarBlockDecl :: Env -> Ident -> Bool
checkVarBlockDecl (_, h:t) ident =
  case Map.lookup ident h of
    Just _ -> True
    Nothing -> False
getVarType :: Env -> Ident -> Err Type
getVarType (_, ctx) ident =
  fnd ctx where
    fnd l = case l of
      t:tt -> case Map.lookup ident t of
        Just x -> return x
        Nothing -> fnd tt
      [] -> fail $ "undeclared variable " ++ show ident
getFunType :: Env -> Ident -> Err FunType
getFunType (ctx, _) ident =
  case Map.lookup ident ctx of
    Just x -> return x
    Nothing -> fail $ "undeclared function " ++ show ident
updateVarType :: Env -> Ident -> Type -> Err Env
updateVarType (x, t:tt) ident typ =
  return (x, Map.insert ident typ t : tt)
updateFunType :: Env -> Ident -> FunType -> Err Env
updateFunType (x, ctx) ident typ =
  case Map.insertLookupWithKey f1 ident typ x of
    (Nothing, r) -> return (r, ctx)
    (Just _, _) -> fail $ "function redefinition: " ++ show ident
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
      "type of " ++
        printTree expr ++
          "expected " ++ printTree typ ++ "but found " ++ printTree typ2

inferExpr :: Env -> Expr -> Err Type
inferExpr env x = case x of
  EVar ident -> getVarType env ident
  ELitInt integer -> return Int
  ELitTrue -> return Bool
  ELitFalse -> return Bool
  EApp ident exprs -> do
    (FunType ret params) <- getFunType env ident
    unless (length params == length exprs) $
      fail $
        "incorrect number of parameters in " ++ printTree x
    zipWithM_ (checkExpr env) params exprs
    return ret
  EString string -> return Str
  Neg expr -> checkExpr env Int expr >> return Int
  Not expr -> checkExpr env Bool expr >> return Bool
  EMul expr1 mulop expr2 -> do
    checkExpr env Int expr1
    checkExpr env Int expr2
    return Int
  EAdd expr1 addop expr2 -> do
    checkExpr env Int expr1
    checkExpr env Int expr2
    return Int
  ERel expr1 relop expr2 -> do
    checkExpr env Int expr1
    checkExpr env Int expr2
    return Bool
  EAnd expr1 expr2 -> do
    checkExpr env Bool expr1
    checkExpr env Bool expr2
    return Bool
  EOr expr1 expr2 -> inferExpr env (EAnd expr1 expr2)

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
          (fail $ "variable " ++ show ident ++ "redeclared in " ++ printTree x)
        updateVarType env1 ident type_
      Init ident expr -> do
        when (checkVarBlockDecl env ident)
          (fail $ "variable " ++ show ident ++ "redeclared in " ++ printTree x)
        checkExpr env type_ expr
        updateVarType env1 ident type_}
  Ass ident expr -> do
    typ <- inferExpr env (EVar ident)
    checkExpr env typ expr
    return env
  Incr ident -> checkExpr env Int (EVar ident) >> return env
  Decr ident -> checkExpr env Int (EVar ident) >> return env
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
      (fail $ "parameter " ++ show ident1 ++ "redeclared in function definition for " ++ show ident)
    updateVarType env1 ident1 type1}
  env2 <- foldM insertArg env args
  let (Block stmts) = block
  void $ checkStmts env2 type_ stmts

checkProgram (Program topdefs) = do
  env1 <- foldM declTopDef emptyEnv topdefs
  let checked = map (checkTopDef env1) topdefs
  if any (not . errToBool) checked then
    let {append a x = case x of
      Ok _ -> a
      Bad e -> a ++ e ++ "\n"}
    in fail $ foldl append "" checked
  else do
    mainType <- getFunType env1 (Ident "main")
    when (mainType /= FunType Void [])
      (fail  "main function has wrong type (should be void())")
    return ()


parse :: String -> Err Program
parse = pProgram . myLexer

getRepr:: Show a => String -> Either String a
getRepr = undefined
