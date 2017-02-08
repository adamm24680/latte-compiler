module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )


import Text.Printf

import Frontend
import IR
import GenIR
import Opt
import Liveness
import GenAsm

genIR p = do
  let l = genProgram p
  let l1 = map propOptFun l
  --let l2 = map deadElimOptFun l1
  let l3 = map livenessAnn l1
  let l4 = genNasmRepr l3
  --let l4 :: [([LiveVars], [Ins Operand])]
  --    l4 = map lineariseAnnotated l3
  --let (l5,_) = unzip $ map (linearScan [0..4]) l4
  let out = unlines $ take 1$ map show l
  let out1 = unlines $ take 1 $ map show l1
  let out2 = unlines $ map show l3
  let out3 = unlines $ l4
  --let out3 = unlines $ take 1 $ map (concatMap show) l5
  putStrLn out
  putStrLn "==============="
  putStrLn out1
  putStrLn "==============="
  putStrLn out2
  putStrLn "==============="
  putStrLn out3
  return l


process :: String -> IO ()
process s = case getRepr s of
          Left e -> do
            putStrLn "Error:"
            putStrLn e
            exitFailure
          Right tree -> do
            print tree
            genIR tree
            exitSuccess


main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "No file specified" >> exitFailure
    fn:_ -> readFile fn >>= process
