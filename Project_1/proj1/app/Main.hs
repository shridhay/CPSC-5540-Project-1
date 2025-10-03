module Main (main) where

import Verifier.Verify
import System.Environment
import System.IO.Error (catchIOError)

main :: IO ()
main = do
    as <- getArgs
    prog <- readFile (head as)
    result <- catchIOError (verify prog) (return . Unknown . show)
    case result of
      Verified -> putStrLn "Verified"
      NotVerified -> putStrLn "Not verified"
      Unknown msg -> putStrLn ("Verifier returned unknown: " ++ msg)
