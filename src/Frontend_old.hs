{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Frontend
  (getRepr, Err, Program, predefs, Type(..), transType)
    where

import qualified Data.Map as Map
import ParLatte
import PrintLatte
import AbsLatte hiding (Type(..))
import qualified AbsLatte (Type(..))
import Control.Monad
import Control.Monad.Reader
import Text.Printf
import qualified ErrM

data Type
    = Int
    | Str
    | Bool
    | Void
    | Array Type
    | Fun Type [Type]
  deriving (Eq, Ord, Show)
instance Print Type where
  prt i e = case e of
    Int -> prPrec i 0 (concatD [doc (showString "int")])
    Str -> prPrec i 0 (concatD [doc (showString "string")])
    Bool -> prPrec i 0 (concatD [doc (showString "boolean")])
    Void -> prPrec i 0 (concatD [doc (showString "void")])
    Array type_ -> prPrec i 0 (concatD [prt 0 type_, doc (showString "[]")])
    Fun type_ types -> prPrec i 0 (concatD [prt 0 type_, doc (showString "("), prt 0 types, doc (showString ")")])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

transType :: AbsLatte.Type a -> Type
transType x = case x of
  AbsLatte.Int _ -> Int
  AbsLatte.Str _ -> Str
  AbsLatte.Bool _ -> Bool
  AbsLatte.Void _ -> Void
  AbsLatte.Array _ type_ -> Array $ transType type_
  AbsLatte.Fun _ type_ types -> Fun (transType type_) (map transType types)

type LineInfo = Maybe (Int, Int)

instance PrintfArg LineInfo where
  formatArg (Just (l, c)) _ = showString $ " line " ++ show l ++ " column " ++ show c
  formatArg Nothing _ = showString ""

data FunType = FunType Type [Type] deriving (Eq)

type VarContext = Map.Map Ident (Type, Bool)
type FunContext = Map.Map Ident FunType
type Env = (FunContext, [VarContext])


instance PrintfArg Ident where
  formatArg (Ident s) _ = showString s

type Err a = ReaderT LineInfo (Either String) a

errToBool :: Err a -> Bool
errToBool e = case runReaderT e Nothing of
  Left _ -> False
  Right _ -> True


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
      [] -> ask >>= \li -> fail $ printf "undeclared variable %s%s" ident li
getFunType :: Env -> Ident -> Err FunType
getFunType (ctx, _) ident =
  case Map.lookup ident ctx of
    Just x -> return x
    Nothing -> ask >>= \li -> fail $ printf "undeclared function %s%s" ident li
updateVarType :: Env -> Ident -> (Type, Bool) -> Err Env
updateVarType (x, t:tt) ident typ =
  return (x, Map.insert ident typ t : tt)
updateFunType :: Env -> Ident -> FunType -> Err Env
updateFunType (x, ctx) ident typ =
  case Map.insertLookupWithKey f1 ident typ x of
    (Nothing, r) -> return (r, ctx)
    (Just _, _) -> ask >>= \li -> fail $ printf "function %s redefined%s" ident li
  where f1 _ _ a = a
enterBlock:: Env -> Env
enterBlock (x, ctx) = (x, Map.empty : ctx)
emptyEnv :: Env
emptyEnv = (Map.empty, [Map.empty])


concatErrors :: [Err a] -> Err ()
concatErrors x = case x of
  h:t -> case runReaderT h Nothing of
    Right _ -> concatErrors t
    Left e -> case runReaderT (concatErrors t) Nothing of
      Right i -> lift $ Right i
      Left e2 -> lift $ Left $ e ++ "\n" ++ e2
  [] -> lift $ Right ()

checkExpr :: Env -> Type -> Expr LineInfo -> Err ()
checkExpr env typ expr = do
  li <- ask
  typ2 <- inferExpr env expr
  unless (typ2 == typ) $
    fail $
      printf "type of %s : expected %s but found %s%s"
        (printTree expr) (printTree typ) (printTree typ2) li

inferExpr :: Env -> Expr LineInfo -> Err Type
inferExpr env x = case x of
  EVar li ident -> local (const li) (fst <$> getVarType env ident)
  ELitInt li _ -> return Int
  ELitTrue _ -> return Bool
  ELitFalse _ -> return Bool
  EApp li ident exprs -> local (const li) $ do
    (FunType ret params) <- getFunType env ident
    li <- ask
    unless (length params == length exprs) $
      fail $ printf
        "incorrect number of parameters in %s%s" (printTree x) li
    zipWithM_ (checkExpr env) params exprs
    return ret
  EString _ _ -> return Str
  Neg li expr -> local (const li) $ checkExpr env Int expr >> return Int
  Not li expr -> local (const li) $ checkExpr env Bool expr >> return Bool
  EMul li expr1 mulop expr2 ->
    local (const li) $ checkTwo Int expr1 expr2 >> return Int
  EAdd li expr1 addop expr2 -> local (const li) $ case addop of
    Minus _ -> checkTwo Int expr1 expr2 >> return Int
    Plus _ -> do
      t1 <- inferExpr env expr1
      t2 <- inferExpr env expr2
      when (t1 /= t2 || t1 /= Str && t1 /= Int)
        (fail $ printf "invalid operands in %s%s" (printTree x) li)
      return t1
  ERel li expr1 relop expr2 ->
    local (const li) $ case relop of
      EQU _ -> checkSame expr1 expr2 >> return Bool
      NE _ -> checkSame expr1 expr2 >> return Bool
      _ -> checkTwo Int expr1 expr2 >> return Bool
  EAnd li expr1 expr2 ->
    local (const li) $ checkTwo Bool expr1 expr2 >> return Bool
  EOr x expr1 expr2 -> inferExpr env (EAnd x expr1 expr2)
  where
    checkTwo type_ expr1 expr2 =
      checkExpr env type_ expr1 >> checkExpr env type_ expr2
    checkSame expr1 expr2 = do
      t1 <- inferExpr env expr1
      checkExpr env t1 expr2

checkStmts :: Env -> Type -> [Stmt LineInfo] -> Err Env
checkStmts env rettype =
  foldM (\env1 stmt -> checkStmt env1 rettype stmt) env

checkStmt :: Env -> Type -> Stmt LineInfo -> Err Env
checkStmt env rettype x = case x of
  Empty _ -> return env
  BStmt _ (Block _ stmts) -> do
    checkStmts (enterBlock env) rettype stmts
    return env
  Decl _ type_ items -> foldM process env items
    where {process env1 item = case item of
      NoInit li ident -> local (const li) $ do
        when (checkVarBlockDecl env ident)
          (fail $ printf "variable %s redeclared in %s%s" ident (printTree x) li)
        updateVarType env1 ident (transType type_, False)
      Init li ident expr -> local (const li) $ do
        when (checkVarBlockDecl env ident)
          (fail $ printf "variable %s redeclared in %s%s" ident (printTree x) li)
        checkExpr env (transType type_) expr
        updateVarType env1 ident (transType type_, False)}
  Ass li ident expr -> local (const li) $ do
    (type_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s%s" ident
      (printTree x) li)
    checkExpr env type_ expr
    return env
  Incr li ident -> local (const li) $ do
    (_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s%s" ident
      (printTree x) li)
    checkExpr env Int (EVar li ident)
    return env
  Decr li ident -> local (const li) $ do
    (_, ro) <- getVarType env ident
    when ro $ fail (printf "parameter %s modified in %s%s" ident
      (printTree x) li)
    checkExpr env Int (EVar li ident)
    return env
  Ret li expr -> local (const li) $ checkExpr env rettype expr >> return env
  VRet li -> unless (rettype == Void) (fail $ printf "return value needed%s" li) >> return env
  Cond li expr stmt -> local (const li) $ do
    checkExpr env Bool expr
    checkStmt env rettype stmt
    return env
  CondElse li expr stmt1 stmt2 -> local (const li) $ do
    checkExpr env Bool expr
    checkStmt env rettype stmt1
    checkStmt env rettype stmt2
    return env
  While x expr stmt -> checkStmt env rettype (Cond x expr stmt)
  SExp _ expr -> inferExpr env expr >> return env


declTopDef :: Env -> TopDef LineInfo -> Err Env
declTopDef env (FnDef li type_ ident args block) =
  local (const li) $
    updateFunType env ident (FunType (transType type_) argtypes)
  where argtypes = map (\(Arg _ type1 _)-> transType type1) args

checkTopDef :: Env -> TopDef LineInfo -> Err ()
checkTopDef env (FnDef li type_ ident args block) = local (const li) $ do
  let {insertArg env1 (Arg liArg type1 ident1) = local (const liArg) $ do
    when (checkVarBlockDecl env1 ident1)
      (fail $ printf "parameter %s redeclared in function definition for %s%s" ident1 ident liArg)
    updateVarType env1 ident1 (transType type1, True)}
  env2 <- foldM insertArg env args
  let (Block _ stmts) = block
  void $ checkStmts env2 (transType type_) stmts
  unless (transType type_ == Void || checkReturnsBlock block) $
    fail $ printf "function %s%s must return a value" ident li


checkReturnsBlock :: Block LineInfo -> Bool
checkReturnsBlock (Block _ stmts) =
  any checkReturnsStmt stmts

checkReturnsStmt :: Stmt LineInfo -> Bool
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
    let {append a x = case runReaderT x Nothing of
      Right _ -> a
      Left e -> a ++ e ++ "\n"}
    in fail $ foldl append "" checked
  else do
    mainType <- getFunType env1 (Ident "main")
    when (mainType /= FunType Int [])
      (fail  "main function has wrong type (should be int())")
    return $ Program i topdefs


parse :: String -> ErrM.Err (Program LineInfo)
parse = pProgram . myLexer

getRepr:: String -> Either String (Program LineInfo)
getRepr s =
  case parse s of
    ErrM.Bad e -> Left e
    ErrM.Ok p -> runReaderT (checkProgram p) Nothing
