import           Control.Exception
import           Control.Monad
import           System.Directory
import           System.Process    (callCommand)
import           Text.Printf

main :: IO ()
main = core >> struct >> bad

core :: IO ()
core = forM_ [1..22] (coreTestCase "good/core")

bad :: IO ()
bad = forM_ [1..27] (testBad "bad/bad")

struct :: IO ()
struct = testCase "extensions/struct/list"

coreTestCase :: String -> Int -> IO ()
coreTestCase base i =
  let name = printf "%s%03d" base i in
  testCase name

testCase :: String -> IO ()
testCase tname = do
  let name = "lattests/" ++ tname
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
  unless (in1 == in2) $ putStrLn ("test " ++ name ++ " failed\n" ++
    unlines (zipWith (curry show) (lines in1) (lines in2)))

testBad :: String -> Int -> IO ()
testBad base i = do
  let name = printf "lattests/%s%03d" base i
  let latFileName = name ++ ".lat"
  (try :: IO a -> IO (Either IOException a)) (callCommand $ "stack exec latc_x86 " ++ latFileName)
  return ()
