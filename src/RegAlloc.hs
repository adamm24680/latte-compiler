{-# LANGUAGE FlexibleInstances #-}
module RegAlloc(linearizeAndAlloc)
  where

import Text.Printf
import Compiler.Hoopl (Graph, O, C)

import Linearscan
import Linearize
import IR
import Liveness (LiveAnnotated)


instance PrintfArg PhysOp where
  formatArg (PhysReg i) _ = showString $ case i of
    0 -> "ebx"
    1 -> "ecx"
    2 -> "edx"
    3 -> "esi"
    4 -> "edi"
    _ -> "__noreg__"
  formatArg (StackSlot i) _ = showString $ "[ebp-" ++ show (4 * (i + 1)) ++ "]"
  formatArg (Constant i) _ = shows i

instance ShowLinRepr [Ins PhysOp] where
  showlr = unlines . map show

linearizeAndAlloc :: QFunDef (Label, Graph LiveAnnotated C C) -> QFunDef [Ins PhysOp]
linearizeAndAlloc = undefined
