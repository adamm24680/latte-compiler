{-# LANGUAGE FlexibleInstances, GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GenAsm
  where

import Text.Printf
import Compiler.Hoopl (Graph, O, C, Label)

import Linearscan
import Linearize
import IR
import Liveness (LiveAnnotated)
import X86DSL
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set


data GenSt = GenSt {
  instrs :: [X86Ins] ,
  funMapping :: Map.Map Ident X86Label,
  counter :: Int,
  externs :: Set.Set String,
  stackOffset :: Int
}

type GenM a = State GenSt a


instance Show (PhysOp X86Reg) where
  show (PhysReg r) = show r
  show (Constant i) = show i
  show (StackSlot i) = "[" ++ show Ebp ++ "-"++ show (4*(i+1))++"]"


emit :: X86Ins -> GenM ()
emit ins =
  modify $ \s -> s{instrs = ins : instrs s}

linearizeAndAlloc :: QFunDef (Label, Graph LiveAnnotated C C) ->
  (QFunDef [Ins (PhysOp X86Reg)], Int)
linearizeAndAlloc (QFunDef ident type_ g params) =
  (QFunDef ident type_ g2 params, i)
  where (g2, i) = linearScan [Ebx, Ecx, Edx, Edi, Esi] $ linearizeAnnotated g

convOp :: PhysOp X86Reg -> X86Op
convOp pr = case pr of
  PhysReg reg -> PReg reg
  Constant i -> PImm $ fromInteger i
  StackSlot i -> PEAddress $ AOff ebp i

toX86Label :: Label -> X86Label
toX86Label l = X86Label $ "." ++ show l

genQ :: Ins X86Op -> GenM ()
genQ (Fst q) = case q of
  QLabel l -> emit $ Label $ toX86Label l
genQ (Mid q) = case q of
  QAlloca d -> do
    modify $ \s -> s{stackOffset = stackOffset s - 4}
    off <- stackOffset <$> get
    emit $ Mov d ebp
    emit $ Add d $ PImm off
genQ (Lst q) = case q of
  QGoto l -> emit $ Jmp $ PLabel $ toX86Label l
  QRet s -> do
    emit $ Mov eax s
    emit $ Jmp $ PLabel $ X86Label ".exit"

genFun :: (QFunDef [Ins (PhysOp X86Reg)], Int) -> GenM ()
genFun (QFunDef ident type_ insns params, locals) = do
  let allocas = length $ filter id $
                  map (\ins -> case ins of
                                Mid (QAlloca _) -> True
                                _ -> False)
                  insns
  let insns2 = map (fmap convOp) insns
  modify $ \s -> s {stackOffset = -4 * locals}

  modify $ \s -> s {stackOffset = 0}

genProgram :: [QFunDef (Label, Graph LiveAnnotated C C)] -> ([X86Ins], [String])
genProgram funlist = undefined
  where
    mapping = Map.fromList $
      zip (map (\(QFunDef ident _ _ _) -> ident) funlist) [1..length funlist]
