import System.Process(callCommand)
import Text.Printf
import System.Directory
import Control.Monad
import Control.Exception

main :: IO ()
main = core >> bad

core :: IO ()
core = forM_ [1..22] (testCase "lattests/good/core")

bad :: IO ()
bad = forM_ [1..27] (testBad "lattests/bad/bad")

testCase :: String -> Int -> IO ()
testCase base i = do
  let name = printf "%s%03d" base i
  let inputName = name ++ ".input"
  let latFileName = name ++ ".lat"
  let outputName = name ++ ".output"
  inputExists <- doesFileExist inputName
  callCommand $ "stack exec latc_x86 " ++ latFileName
  if inputExists then
    callCommand $ printf "cat %s | %s > out" inputName name
  else
    callCommand $ printf "%s > out" name
  in1 <- readFile "out"
  in2 <- readFile outputName
  unless (in1 == in2) $ putStrLn ("test " ++ show i ++ " failed\n"++ (unlines $ map show $ zip (lines in1) (lines in2)))

testBad :: String -> Int -> IO ()
testBad base i = do
  let name = printf "%s%03d" base i
  let latFileName = name ++ ".lat"
  (try :: IO a -> IO (Either IOException a)) (callCommand $ "stack exec latc_x86 " ++ latFileName)
  return ()
