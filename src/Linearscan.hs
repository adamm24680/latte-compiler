{-# LANGUAGE GADTs #-}
module Linearscan (linearScan, PhysOp (..))
  where

import           IR
import           Linearize
import           Liveness

import           Control.Monad.State
import qualified Data.Map            as Map
import           Data.Maybe
import qualified Data.Set            as Set


data PhysOp t = PhysReg t | Constant Integer | StackSlot Int| NoReg deriving Eq


data LsState t = LsState {
  mapping ::  Map.Map Operand t,
  free    :: [t],
  active  :: Set.Set Operand,
  spilled :: Set.Set Operand,
  dump    :: [String]
}


type LsM t a = State (LsState t) a

lsra :: LiveRanges -> Int -> LsM t (Map.Map Operand t, Set.Set Operand)
lsra ranges n = do
  forM_ [0..n] $ \pc ->
    case getLiveStarts pc ranges of
      Nothing -> return ()
      Just newregs -> do
        freeRegs ranges pc
        forM_ newregs $ \reg -> do
          lfree <- free <$> get
          if null lfree then
            spillReg ranges reg
          else
            assignReg reg
  state <- get
  return (mapping state, spilled state)

assignReg :: Operand -> LsM t ()
assignReg op =
  modify (\s -> s {mapping = Map.insert op (head $ free s) $ mapping s,
                   free = tail $ free s,
                   active = Set.insert op $ active s})

freeReg :: Operand -> LsM t ()
freeReg reg = do
  lmapping  <- mapping <$> get
  let hreg = fromJust $ Map.lookup reg lmapping
  modify $ \s -> s {active = Set.delete reg $ active s,
                    free = hreg : free s}


freeRegs :: LiveRanges -> Int -> LsM t ()
freeRegs ranges pc = do
  lactive <- active <$> get
  forM_ lactive $ \reg ->
    when (getLiveEnd reg ranges <= pc) $ freeReg reg

spillReg :: LiveRanges -> Operand -> LsM t ()
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


linearScan :: Eq t => [t] -> ([LiveVars], [Ins Operand]) -> ([Ins (PhysOp t)], Int)
linearScan regs (anns, prog) =
  (filter filterTrivial $ map (fmap mappingFun) prog, Set.size spills)
  where
    ranges = computeLiveRanges anns
    (mapped, spills) =
      evalState (lsra ranges $ length prog)
        LsState {mapping = Map.empty, free = regs,
                 active = Set.empty, spilled = Set.empty, dump=[] }
    spillMap = Map.fromList $ zip (Set.toList spills) [0.. Set.size spills - 1]
    mappingFun (LitInt i) = Constant i
    mappingFun reg =
      case Map.lookup reg mapped of
        Just regid -> PhysReg regid
        Nothing -> case Map.lookup reg spillMap of
          Just i  -> StackSlot i
          Nothing -> NoReg
    filterTrivial ins = case ins of
      Mid (QCopy a1 a2) -> a1 /= a2
      _                 -> True
