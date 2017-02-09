import System.Process(callCommand)
import Text.Printf
import System.Directory
import Control.Monad

main :: IO ()
main = core

core :: IO ()
core = forM_ [4..22] (testCase "lattests/good/core")

testCase :: String -> Int -> IO ()
testCase base i = do
  let name = printf "%s%03d" base i
  let inputName = name ++ ".input"
  let latFileName = name ++ ".lat"
  let outputName = name ++ ".output"
  inputExists <- doesFileExist inputName
  callCommand $ "stack exec latc-exe " ++ latFileName
  if inputExists then
    callCommand $ printf "cat %s | %s > out" inputName name
  else
    callCommand $ printf "%s > out" name
  in1 <- readFile "out"
  in2 <- readFile outputName
  unless (in1 == in2) $ putStrLn ("test " ++ show i ++ " failed\n"++ (unlines $ map show $ zip (lines in1) (lines in2)))
