module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )

import Frontend
import ErrM
import AbsLatte

process :: String -> IO ()
process s = case getRepr s of
          Bad e -> do
            putStrLn "Error:"
            putStrLn e
            exitFailure
          Ok tree -> do
            print (tree::Program)
            exitSuccess


main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "No file specified" >> exitFailure
    fn:_ -> readFile fn >>= process
