import System.Process(callCommand)
import Text.Printf
import System.Directory
import Control.Monad

main :: IO ()
main = core

core :: IO ()
core = forM_ [1..18] (testCase "lattests/good/core")

testCase :: String -> Int -> IO ()
testCase name i = do
  let name = printf "%s%03d" name i
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
  unless (in1 == in2) $ print ("test " ++ show i ++ " failed")
