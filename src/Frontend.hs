module Frontend
  (getRepr, Err, Program)
    where

import qualified Data.Map as Map
import ErrM
import ParLatte
import PrintLatte
import AbsLatte

data FunType = FunType Type [Type]

type VarContext = Map.Map Ident Type
type FunContext = Map.Map Ident FunType
type Env = (FunContext, [VarContext])

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

parse :: String -> Err Program
parse = pProgram . myLexer

getRepr:: Show a => String -> Either String a
getRepr = undefined
