module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )

import Frontend
import IR
import GenIR
import Opt
import RegAlloc

import Liveness (livenessAnn)
import Linearise

lingraph g = concatMap show ins
  where
    (_, ins) = lineariseAnnotated $ livenessAnn g

genIR p = do
  let l = genProgram p
  let l1 = map propOptFun l
  let l2 = map deadElimOptFun l1
  let l3 = map lingraph l2
  let out = unlines $ take 1$ map show l
  let out1 = unlines $ take 1 $ map show l1
  let out2 = unlines $ take 1 $ map show l2
  let out3 = unlines $ take 1 $ l3
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
