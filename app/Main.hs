module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )

import Frontend
import IR


genIR p = do
  let l = genProgram p
  let out = unlines $ map show l
  putStrLn out
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
