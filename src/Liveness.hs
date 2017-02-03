{-# LANGUAGE GADTs, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Liveness (computeLiveRanges, livenessAnn, LiveAnnotated(..),
    mkLiveAnnotated, LiveVars, LiveRanges, getLiveStarts, getLiveEnd)
  where

import AbsLatte (Ident)
import IR ( Quad(..), Operand(..), BinOp(..), CompOp(..), QFunDef(..))
import Compiler.Hoopl
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State

type LiveVars = Set.Set Operand

data LiveAnnotated e x = LiveAnnotated (LiveVars, Quad Operand e x)

mkLiveAnnotated :: Quad Operand e x -> LiveAnnotated e x
mkLiveAnnotated q = LiveAnnotated (Set.empty, q)

instance Show (LiveAnnotated e x) where
  show (LiveAnnotated(s, q)) =show q++"\n"++"Live vars: " ++ show (Set.toList s)


instance NonLocal LiveAnnotated where
  entryLabel (LiveAnnotated(_, q)) = entryLabel q
  successors (LiveAnnotated(_, q)) = successors q

liveLattice :: DataflowLattice LiveVars
liveLattice = DataflowLattice {
  fact_name = "live registers" ,
  fact_bot = Set.empty,
  fact_join = join
} where
  join _ (OldFact old) (NewFact new) = (ch, j)
    where
      j = Set.union new old
      ch = changeIf (Set.size j > Set.size old)

liveTransfer :: BwdTransfer LiveAnnotated LiveVars
liveTransfer = mkBTransfer tr
  where
    tr :: LiveAnnotated e x -> Fact x LiveVars -> LiveVars
    tr (LiveAnnotated (_, q)) f = case q of
      QLabel _  -> f
      QCopy d s -> addUse s $ delUse d f
      QBinOp d op s1 s2 -> update2 d s1 s2 f
      QCompOp d op s1 s2 -> update2 d s1 s2 f
      QAnd d s1 s2 -> update2 d s1 s2 f
      QOr d s1 s2 -> update2 d s1 s2 f
      QNeg d s -> update1 d s f
      QNot d s -> update1 d s f
      QLoad d s -> update1 d s f
      QStore d s -> addUse d $ addUse s f
      QGoto l -> factL f l
      QGotoBool r l1 l2 -> addUse r $ factL f l1 `Set.union` factL f l2
      QParam r -> addUse r f
      QCall _ _ -> f
      QCallExternal _ _ -> f
      QVRet -> fact_bot liveLattice
      QRet r -> addUse r $ fact_bot liveLattice
      QAlloca d -> delUse d f
      QError -> fact_bot liveLattice
      QLoadParam d _ -> delUse d f
    delUse = Set.delete
    addUse o f =
      case o of
        LitInt _ -> f
        _ -> Set.insert o f
    update2 d s1 s2 f = addUse s1 $ addUse s2 $ delUse d f
    update1 d s f = addUse s $ delUse d f
    factL factbase l = fromMaybe Set.empty $ lookupFact l factbase

deadElimRewrite :: FuelMonad m => BwdRewrite m LiveAnnotated LiveVars
deadElimRewrite = mkBRewrite3 elimCO elimOO elimOC
  where
    elimOO :: Monad m => LiveAnnotated O O -> Fact O LiveVars -> m (Maybe (Graph LiveAnnotated O O))
    elimOO (LiveAnnotated(_, q)) f = return $ case q of
      QCopy d _ -> elimIf d
      QBinOp d _ _ _ -> elimIf d
      QCompOp d _ _ _ -> elimIf d
      QAnd d _ _ -> elimIf d
      QOr d _ _ -> elimIf d
      QNeg d _ -> elimIf d
      QNot d _ -> elimIf d
      QLoad d _ -> elimIf d
      QAlloca d -> elimIf d
      QLoadParam d _ -> elimIf d
      _ -> Just $ mkMiddle $ LiveAnnotated (f, q)
      where
        elimIf d =
          if not (Set.member d f) then
            Just emptyGraph
          else
            Just $ mkMiddle $ LiveAnnotated (f, q)
    elimCO (LiveAnnotated(_, q)) f =
      return $ Just $ mkFirst $ LiveAnnotated (f, q)
    elimOC :: Monad m => LiveAnnotated O C -> Fact C LiveVars -> m (Maybe (Graph LiveAnnotated O C))
    elimOC (LiveAnnotated(_, q)) f =
      let scc = successors q
          facts = map (fromMaybe (fact_bot liveLattice) . (`lookupFact` f)) scc
          f1 = foldl Set.union Set.empty facts
      in
        return $ Just $ mkLast $ LiveAnnotated (f1, q)

deadElimPass :: FuelMonad m => BwdPass m LiveAnnotated LiveVars
deadElimPass = BwdPass {
  bp_lattice = liveLattice,
  bp_transfer = liveTransfer,
  bp_rewrite = deadElimRewrite
}

livenessAnn :: QFunDef Operand -> (Label, Graph LiveAnnotated C C)
livenessAnn (QFunDef ident type_ (l, graph) params) = (l, newgraph)
  where
    graph2 = mapGraph mkLiveAnnotated graph
    (newgraph, _, _) = runSimpleUniqueMonad $
      (runWithFuel :: Monad m => Fuel -> InfiniteFuelMonad m a -> m a) infiniteFuel $
        analyzeAndRewriteBwd deadElimPass (JustC [l]) graph2 mapEmpty

type LiveStart = Map.Map Int [Operand]
type LiveEnd = Map.Map Operand Int
data LiveRanges = LiveRanges LiveStart LiveEnd

getLiveEnd :: Operand -> LiveRanges -> Int
getLiveEnd op (LiveRanges _ le) = fromJust $ Map.lookup op le

getLiveStarts :: Int -> LiveRanges -> Maybe [Operand]
getLiveStarts i (LiveRanges ls _) = Map.lookup i ls

data LiveStateData = LiveStateData
  { active :: LiveVars
  , lannos :: [LiveVars]
  , lstarts :: LiveStart
  , lends :: LiveEnd
  , pcCnt :: Int
  }

type LiveState a = State LiveStateData a

computeLiveRanges :: [LiveVars] -> LiveRanges
computeLiveRanges liveannos = LiveRanges ls le
  where
    endstate = execState step initstate
    ls = lstarts endstate
    le = lends endstate
    initstate = LiveStateData
                  { active = Set.empty
                  , lannos = liveannos
                  , lstarts = Map.empty
                  , lends = Map.empty
                  , pcCnt = 0
                  }

step :: LiveState ()
step = do
  annos <- lannos <$> get
  unless (null annos) $ do
    pc <- pcCnt <$> get
    let (la:las) = annos
    lsmap <- lstarts <$> get
    lemap <- lends <$> get
    cur <- active <$> get
    let new = Set.toList $ la `Set.difference` cur
    let dead = cur `Set.difference` la

    let alt Nothing = Just new
        alt (Just old) = Just $ new ++ old
    modify (\s -> s { lannos = las,
                      active = la,
                      lstarts = Map.alter alt pc lsmap,
                      lends = Set.fold (`Map.insert` pc) lemap dead
                    })
    incPC
    step

incPC :: LiveState ()
incPC = modify (\s -> s { pcCnt = 1 + pcCnt s })
