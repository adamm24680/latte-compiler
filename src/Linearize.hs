{-# LANGUAGE GADTs #-}

module Linearize (Ins(..), linearizeAnnotated)
  where

import           Compiler.Hoopl
import           Text.Printf

import           IR
import           Liveness


linearizeAnnotated :: (Label, Graph LiveAnnotated C C) -> ([LiveVars], [Ins Operand])
linearizeAnnotated (entry, g) = unzip $ concatMap linearizeBlock blocks
  where
    entryseq = mkLast $ mkLiveAnnotated $ QGoto entry
    blocks = postorder_dfs $ entryseq |*><*| g
    linearizeBlock :: Block LiveAnnotated C C -> [(LiveVars, Ins Operand)]
    linearizeBlock b = fst1 ++ mid1 ++ lst1
      where
        (fsts, mids, lasts) = blockSplitAny b
        fst1 :: [(LiveVars, Ins Operand)]
        fst1 = case fsts of
          JustC (LiveAnnotated(ann, n)) -> [(ann, Fst n)]
        lst1 = case lasts of
          JustC (LiveAnnotated(ann, n)) -> [(ann, Lst n)]
        mid1 = map (\(LiveAnnotated(a, q)) -> (a, Mid q)) $ blockToList mids
