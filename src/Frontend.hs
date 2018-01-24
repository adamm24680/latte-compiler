{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Frontend
  --(getRepr, Err, Program, predefs, Type(..), transType)
    where

import           AbsLatte
import           Control.Monad
import           Control.Monad.Reader
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
data ClassSig= ClassSig {super :: Maybe Ident,
                    fields     :: [(Ident, VType)],
                    methods    :: [(Ident, FunSig)]}
data GlobalEnv = GlobalEnv [(Ident, ClassSig)] [(Ident, FunSig)]
data FrontendEnv = FrontendEnv { globalEnv :: GlobalEnv,
                                lineData   :: LineData}
type FrontendM = ReaderT FrontendEnv (Either String)

updateGlobalEnv :: Show a => GlobalEnv -> TopDef a -> Err GlobalEnv
updateGlobalEnv (GlobalEnv cl fl) (FnDef li type_ ident args _) =
  if isJust $ lookup ident fl then
    Left $ "global function " ++ show ident ++ "redeclared" ++ show li
  else
    Right $ GlobalEnv cl ((ident, funtype) : fl)
    where
      argtypes = map (\(Arg _ argtype _) -> void argtype) args
      funtype = FunSig (void type_) argtypes
updateGlobalEnv (GlobalEnv cl fl) (ClassDef li ident classext classels) = do
  when (isJust $ lookup ident cl) $
    Left ("class " ++ show ident ++ "redeclared" ++ show li )
  case classext of
    Extends exli exident -> when (isNothing $ lookup exident cl) $
      Left ("unknown superclass " ++show exident ++
        " in declaration of " ++ show ident++ show exli)
    NoExtend _ -> return ()
  methods1 <- foldM processMethodSignature [] classels
  fields1 <- foldM processFieldDecl [] classels
  let class_ = ClassSig {super = Nothing, fields = fields1, methods = methods1}
  return $ GlobalEnv ((ident, class_):cl) fl
  where
    processMethodSignature :: Show a => [(Ident, FunSig)] -> ClassEl a -> Err [(Ident, FunSig)]
    processMethodSignature ml (MethodDef li type_ ident args _) = do
      let sig = FunSig (void type_) $ map (\(Arg _ argtype _) -> void argtype) args
      when (isJust $ lookup ident fl) $
        Left $ "global function " ++ show ident ++ "redeclared" ++ show li
      when (isJust $ lookup ident ml) $
        Left $ "class method " ++ show ident ++ "redeclared" ++ show li
      Right $ (ident, sig) : ml
    processMethodSignature x _ = return x
    processFieldDecl :: Show a => [(Ident, VType)] -> ClassEl a -> Err [(Ident, VType)]
    processFieldDecl fieldl (FieldDef li type_ idents) = do
      let {checkInnerRedeclaration i =
        when (isJust $ lookup i fieldl) $
          Left ("class field " ++ show ident ++ " redeclared" ++ show li)}
      case classext of
        NoExtend _ -> return ()
        Extends _ superIdent ->
          let errorS = "superclass field " ++ show ident ++ " redeclared" ++ show li in
          forM_ idents $
            \i -> when (checkOuterRedeclaration cl i superIdent) (Left errorS)
      mapM_ checkInnerRedeclaration idents
      return $ fieldl ++ map (\i -> (i, void type_)) idents
    processFieldDecl x _ = return x

generateSignatures :: Show a => Program a -> Err GlobalEnv
generateSignatures (Program _ defs) =
  foldM updateGlobalEnv (GlobalEnv [] []) defs


checkOuterRedeclaration :: [(Ident, ClassSig)] -> Ident -> Ident -> Bool
checkOuterRedeclaration cl ident superIdent =
  case lookup superIdent cl of
    Nothing -> error "internal error"
    Just superSig ->
      case lookup ident $ fields superSig of
        Just _ -> True
        Nothing -> case super superSig of
          Just superSuperIdent ->
            checkOuterRedeclaration cl ident superSuperIdent
          Nothing -> False


checkReturnsStmt :: Stmt a -> Bool
checkReturnsStmt x = case x of
  Empty _ -> False
  BStmt _ (Block _ stmts) ->
    any checkReturnsStmt stmts
  Decl _ type_ items -> False
  Ass _ ident expr -> False
  Incr _ ident -> False
  Decr _ ident -> False
  Ret _ expr -> True
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
  SExp _ expr -> False

annotateTree :: Program LineData -> Program VType
annotateTree (Program _ topdefs) = undefined
