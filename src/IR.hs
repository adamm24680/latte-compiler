{-# LANGUAGE FlexibleInstances, GADTs, StandaloneDeriving #-}
module IR (Operand(..), Label, Quad(..), BinOp(..), CompOp(..), QFunDef(..))
  where

import qualified Data.Map as Map
import Text.Printf
import Compiler.Hoopl (Label,C, O, NonLocal, entryLabel, successors, Graph, showGraph)
import AbsLatte

instance PrintfArg Ident where
  formatArg (Ident s) _ = showString s

data Operand = Reg String
  |LitInt Integer
  -- |Local Ident
  deriving(Eq, Ord)
instance Show Operand where
  show (Reg i) = i
  show (LitInt i) = show i
instance PrintfArg Operand where
  formatArg x _ = case x of
    Reg s -> showString s
    LitInt i -> shows i
    --Local (Ident s) -> showString s

data BinOp = QAdd | QSub | QMul | QDiv | QMod deriving(Eq)
instance PrintfArg BinOp where
  formatArg x _ = showString $ case x of
    QAdd -> "+"
    QSub -> "-"
    QMul -> "*"
    QDiv -> "/"
    QMod -> "%"
data CompOp = L | LE | G | GE | E | NE deriving(Eq)
instance PrintfArg CompOp where
  formatArg x _ = showString $ case x of
    L -> "<"
    IR.LE -> "<="
    G -> ">"
    IR.GE -> ">="
    E -> "=="
    IR.NE -> "!="

--newtype Label = Label String deriving (Show)
instance PrintfArg Label where
   formatArg l _ = shows l


data Quad e x where
  QBinOp :: Operand -> BinOp -> Operand -> Operand -> Quad O O
  QCompOp :: Operand -> CompOp -> Operand -> Operand -> Quad O O
  QAnd :: Operand -> Operand -> Operand -> Quad O O
  QOr :: Operand -> Operand -> Operand -> Quad O O
  QNeg :: Operand -> Operand -> Quad O O
  QNot :: Operand -> Operand -> Quad O O
  QLoad :: Operand -> Operand -> Quad O O
  QStore :: Operand -> Operand -> Quad O O
  QCopy :: Operand -> Operand -> Quad O O
  QGoto :: Label -> Quad O C
  QGotoBool :: Operand -> Label -> Label -> Quad O C
  QParam :: Operand -> Quad O O
  QCall :: Operand -> Ident -> Quad O O
  QCallExternal :: Operand -> String -> Quad O O
  QLabel :: Label -> Quad C O
  --QPhi :: Operand -> Operand -> Operand -> Quad O O
  QVRet :: Quad O C
  QRet :: Operand -> Quad O C
  QAlloca :: Operand -> Quad O O
  QError :: Quad O C

deriving instance Eq (Quad x e)

instance NonLocal Quad where
  entryLabel (QLabel l) = l
  successors (QRet _) = []
  successors QVRet = []
  successors QError = []
  successors (QGoto l) = [l]
  successors (QGotoBool _ l1 l2) = [l1, l2]


instance Show (Quad e x) where
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
     --QPhi d s1 s2 -> printf "  %s = phi(%s, %s)" d s1 s2
     QVRet -> "  ret"
     QRet r -> printf "  ret %s" r
     QLabel l -> printf "%s:" l
     QAlloca d -> printf "  %s = alloca" d
     QError -> printf "  error()"

data QFunDef = QFunDef Ident Type (Label, Graph Quad C C) Integer

instance Show QFunDef where
  show (QFunDef (Ident ident) type_ (entry, graph) params) =
    printf "function %s(%d) {\n%s}" ident params $
      showGraph show graph
