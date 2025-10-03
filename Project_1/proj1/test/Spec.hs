import Verifier.Verify

import Data.List (findIndices)
import Data.Maybe (fromMaybe)
import GHC.IO.Handle (hFlush)
import GHC.IO.StdHandles (stdout)
import GHC.Utils.Misc (uncurry3)
import System.Directory (listDirectory)
import System.Exit (die)
import System.IO.Error (catchIOError)
import System.Timeout (timeout)

main :: IO ()
main = do
  let benchmarksPath = "./benchmarks/"
  let sets = [ ("provided invalid", NotVerified, benchmarksPath ++ "invalid/")
             , ("provided valid", Verified, benchmarksPath ++ "valid/")
             ]
  results <- mapM (uncurry3 testSet) sets
  if or results
    then die ""
    else putStrLn "All tests succeeded"

testSet :: String -> Result -> String -> IO Bool
testSet set desiredOutput path = do
  putStrLn $ unwords ["Testing set", show set]
  files <- listDirectory path
  output <- mapM testOne (map (path ++) files)
  let failures = findIndices (desiredOutput /=) output
  let numberTests = length files
  let numberFailures = length failures
  let didFail = numberFailures > 0
  let detailString =
        unwords $ ["succeeded on"
                  , show (numberTests - numberFailures)
                  , "/"
                  , show numberTests
                  , "files"
                  ] ++ if didFail
                  then [ "and failed on"
                       , show (numberFailures)
                       , "files:"
                       ] ++ map (show . \index -> (files !! index, output !! index)) failures
                  else []
  putStrLn . unwords $ ["Set", show set, detailString]
  return didFail

testOne :: String -> IO Result
testOne file = do
  putStr $ "Checking " ++ file ++ "..."
  hFlush stdout
  prog <- readFile file
  result <- timeout (60 * 1000000) (catchIOError (verify prog) (return . Unknown . show))
  putStrLn "done"
  return $ fromMaybe (Unknown "timeout") result
