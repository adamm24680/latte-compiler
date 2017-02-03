{-# LANGUAGE GADTs #-}
module Linearscan (linearScan, PhysOp (..))
  where

import Liveness
import IR
import Linearise

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Data.Maybe

type RegId = Int

data PhysOp = PhysReg RegId | Constant Integer | StackSlot Int deriving Eq

type RegMap = Map.Map Operand RegId

data LsState = LsState {
  mapping :: RegMap,
  free :: [RegId],
  active :: Set.Set Operand,
  spilled :: Set.Set Operand,
  dump :: [String]
}


type LsM a = State LsState a

lsra :: LiveRanges -> Int -> LsM (RegMap, Set.Set Operand, [String])
lsra ranges n = do
  forM_ [0..n] $ \pc -> do
    st <-get
    let d2 = show (free st) ++ show (Map.toList $ mapping st) ++
                show (Set.toList $ active st) ++ show (Set.toList $ spilled st)
    put $ st {dump = d2 : dump st}
    case getLiveStarts pc ranges of
      Nothing -> return ()
      Just newregs -> do
        freeRegs ranges pc
        forM_ newregs $ \reg -> do
          lfree <- free <$> get
          if null lfree then
            spillReg ranges reg
          else do
            assignReg reg
            --s <- get
            --error $ show (free s) ++ show (Map.toList $ mapping s)
  state <- get
  return (mapping state, spilled state, reverse $dump state)

assignReg :: Operand -> LsM ()
assignReg op =
  modify (\s -> s {mapping = Map.insert op (head $ free s) $ mapping s,
                   free = tail $ free s,
                   active = Set.insert op $ active s})

freeReg :: Operand -> LsM ()
freeReg reg = do
  lmapping  <- mapping <$> get
  let hreg = fromJust $ Map.lookup reg lmapping
  modify $ \s -> s {active = Set.delete reg $ active s,
                    free = hreg : free s}


freeRegs :: LiveRanges -> Int -> LsM ()
freeRegs ranges pc = do
  lactive <- active <$> get
  forM_ lactive $ \reg ->
    when (getLiveEnd reg ranges <= pc) $ freeReg reg

spillReg :: LiveRanges -> Operand -> LsM ()
spillReg ranges reg = do
  lactive <- active <$> get
  let lr = getLiveEnd reg ranges
  let opr = filter (\(_,r) -> r>lr) $
              map (\x -> (x, getLiveEnd x ranges)) $ Set.toList lactive
  case opr of
    (op, _):_-> do
      freeReg op
      assignReg reg
      modify $ \s -> s {mapping = Map.delete op $ mapping s,
                        spilled = Set.insert op $ spilled s}
    [] -> modify $ \s -> s{spilled = Set.insert reg $ spilled s}


linearScan :: [RegId] -> ([LiveVars], [Ins Operand]) -> ([Ins PhysOp], Int)
linearScan regs (anns, prog) =
  (filter filterTrivial $ map (fmap mappingFun) prog, Set.size spills)
  where
    ranges = computeLiveRanges anns
    (mapped, spills, dump) =
      evalState (lsra ranges $ length prog)
        LsState {mapping = Map.empty, free = regs,
                 active = Set.empty, spilled = Set.empty, dump=[] }
    spillMap = Map.fromList $ zip (Set.toList spills) [0.. Set.size spills - 1]
    mappingFun (LitInt i) = Constant i
    mappingFun reg = w
      where
        w = case Map.lookup reg mapped of
          Just regid -> PhysReg regid
          Nothing -> case Map.lookup reg spillMap of
            Just i -> StackSlot i
            Nothing -> error "unallocated register in linearscan - should not happen"
    filterTrivial ins = case ins of
      Mid (QCopy a1 a2) -> a1 /= a2
      _ -> True
