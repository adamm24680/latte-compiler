module Main where

import System.IO ( hPutStrLn, stderr )
import System.Environment ( getArgs)
import System.Exit ( exitFailure, exitSuccess )
import System.FilePath
import System.Directory
import Control.Monad(when, unless)
import System.Process(callCommand)


import Text.Printf

import Frontend
import GenIR
import Opt
import Liveness
import GenAsm

genIR :: (Program VType, GlobalEnv) -> IO String
genIR p = do
  let l = genProgram p
  let l1 = map propOptFun l
  --let l2 = map deadElimOptFun l1
  let l3 = map livenessAnn l1
  let l4 = genNasmRepr l3
  --let l4 :: [([LiveVars], [Ins Operand])]
  --    l4 = map lineariseAnnotated l3
  --let (l5,_) = unzip $ map (linearScan [0..4]) l4
  return $ unlines l4

runFile :: FilePath -> IO ()
runFile f = do
  exists <- doesFileExist f
  unless exists $ hPutStrLn stderr "File not found" >> exitFailure
  let fn = dropExtension . takeFileName $ f
  let dir = takeDirectory f
  readFile f >>= process fn dir

process :: String -> FilePath -> String -> IO ()
process name dir s =
  case getRepr s of
    Left e -> do
      putStrLn "Error:"
      putStrLn e
      exitFailure
    Right tree -> do
      res <- genIR tree
      let outputFn = dir </> name <.> "s"
      let outputObjFn = dir </> name <.> "o"
      let outputExeFn = dir </> name
      writeFile outputFn res
      putStrLn $ "wrote " ++ outputFn
      callCommand $ unwords ["nasm", "-f", "elf32", "-o",  outputObjFn, outputFn]
      callCommand $
        unwords ["gcc", "-m32", "-o",  outputExeFn, outputObjFn, "lib/runtime.o"]
      exitSuccess

main :: IO ()
main = do
  args <- getArgs
  case args of
    [filename] -> runFile filename
    [] -> hPutStrLn stderr "No input file specified..." >> exitFailure
    _ -> hPutStrLn stderr "Too many input files..." >> exitFailure
  exitSuccess
