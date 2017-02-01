{-# LANGUAGE FlexibleInstances, GADTs, StandaloneDeriving #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module IR (Operand(..), Label, Quad(..), BinOp(..), CompOp(..), QFunDef(..))
  where

import qualified Data.Map as Map
import Text.Printf
import Compiler.Hoopl (Label, C, O, NonLocal(..), Graph, showGraph, HooplNode(..))
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


data Quad t e x where
  QBinOp :: t -> BinOp -> t -> t -> Quad t O O
  QCompOp :: t -> CompOp -> t -> t -> Quad t O O
  QAnd :: t -> t -> t -> Quad t O O
  QOr :: t -> t -> t -> Quad t O O
  QNeg :: t -> t -> Quad t O O
  QNot :: t -> t -> Quad t O O
  QLoad :: t -> t -> Quad t O O
  QStore :: t -> t -> Quad t O O
  QCopy :: t -> t -> Quad t O O
  QGoto :: Label -> Quad t O C
  QGotoBool :: t -> Label -> Label -> Quad t O C
  QParam :: t -> Quad t O O
  QCall :: t -> Ident -> Quad t O O
  QCallExternal :: t -> String -> Quad t O O
  QLabel :: Label -> Quad t C O
  --QPhi :: t -> t -> t -> Quad O O
  QVRet :: Quad t O C
  QRet :: t -> Quad t O C
  QAlloca :: t -> Quad t O O
  QError :: Quad t O C
  QLoadParam :: t -> Int -> Quad t O O
deriving instance Eq t => Eq (Quad t e x)

instance NonLocal (Quad t) where
  entryLabel (QLabel l) = l
  successors (QRet _) = []
  successors QVRet = []
  successors QError = []
  successors (QGoto l) = [l]
  successors (QGotoBool _ l1 l2) = [l1, l2]

instance HooplNode (Quad t) where
  mkBranchNode = QGoto
  mkLabelNode = QLabel

instance Show (Quad Operand e x) where
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
     QLoadParam d i -> printf "  %s = loadParam %d" d i

data QFunDef = QFunDef Ident Type (Label, Graph (Quad Operand) C C) Integer

instance Show QFunDef where
  show (QFunDef (Ident ident) type_ (entry, graph) params) =
    printf "function %s(%d) {\n%s}" ident params $
      showGraph show graph
