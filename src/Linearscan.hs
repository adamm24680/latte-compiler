module Linearscan
  where

import Liveness
import IR
import Linearise

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Data.Maybe

type RegId = Int

data PhysOp = Reg RegId | Constant Integer | StackSlot Int

type RegMap = Map.Map Operand RegId

data LsState = LsState {
  mapping :: RegMap,
  free :: [RegId],
  active :: Set.Set Operand,
  pc :: Int,
  acc :: [Ins PhysOp],
  spilled :: Set.Set Operand
}


type LsGen a = State LsState a

lsra :: LiveRanges -> Int -> LsGen ()
lsra ranges n =
  forM_ [1..n] $ \pc ->
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

assignReg :: Operand -> LsGen ()
assignReg op =
  modify (\s -> s {mapping = Map.insert op (head $ free s) $ mapping s,
                   free = tail $ free s,
                   active = Set.insert op $ active s})

freeReg :: Operand -> LsGen ()
freeReg reg = do
  lmapping  <- mapping <$> get
  let hreg = fromJust $ Map.lookup reg lmapping
  modify $ \s -> s {active = Set.delete reg $ active s,
                    free = hreg : free s}

freeRegs ranges pc = do
  lactive <- active <$> get
  forM_ lactive $ \reg ->
    when (getLiveEnd reg ranges < pc) $ freeReg reg

spillReg ranges reg = undefined

linearScan :: ([LiveVars], [Ins Operand]) -> ([Ins PhysOp], Int)
linearScan (anns, prog) = undefined
  where
    ranges = computeLiveRanges anns
    mapping = undefined
