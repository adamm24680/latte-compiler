{-# LANGUAGE GADTs #-}
module Opt where

import AbsLatte (Ident)
import IR ( Quad(..), Operand(..), BinOp(..), CompOp(..))
import Compiler.Hoopl
import Data.Dynamic
import Data.Maybe


splitBlocks :: [Dynamic] -> [Dynamic] -> [[Dynamic]] -> [[Dynamic]]
splitBlocks l cur acc =
  case l of
    h : t -> case (fromDynamic :: Dynamic -> Maybe (Quad C O)) h of
      Just _ -> splitBlocks t [h] (reverse cur : acc)
      Nothing -> splitBlocks t (h: cur) acc
    [] -> reverse acc

splitBlock :: [Dynamic] -> (Quad C O, [Quad O O], Quad O C)
splitBlock l =
  let flt fun = map fromJust . filter (Nothing /=) . map fun
      entry = head . flt (fromDynamic :: Dynamic -> Maybe (Quad C O)) $ l
      exit =  head . flt (fromDynamic :: Dynamic -> Maybe (Quad O C)) $ l
      middle = flt (fromDynamic :: Dynamic -> Maybe (Quad O O)) l
  in undefined
