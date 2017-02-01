module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )

import Frontend
import IR
import GenIR
import Opt


genIR p = do
  let l = genProgram p
  let l1 = map constPropOptFun l
  let out = unlines $ take 1$ map show l
  let out1 = unlines $ take 1 $ map show l1
  putStrLn out
  putStrLn "==============="
  putStrLn out1
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
