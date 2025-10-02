module Verifier.Verify (Result(..), verify) where

import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Lazy.Char8 as LC

import Verifier.GC
import Parser.Parser

import SMTLIB.Backends (QueuingFlag (..), command, command_, initSolver)
import qualified SMTLIB.Backends.Z3 as Z3

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify progString = do 
  case (parseProg progString) of 
    Nothing -> return (Unknown "Parsing failed")
    Just p -> do 
      let z3string = getZ3String p
      Z3.with Z3.defaultConfig $ \handle -> do
        solver <- initSolver Queuing (Z3.toBackend handle)
        res <- command solver (B.stringUtf8 z3string)
        case (LC.unpack res) of
          "sat\n" -> return NotVerified
          "unsat\n" -> return Verified
          s -> return (Unknown s)
