module Verify (Result(..), verify) where

import Lexer
import Language

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify _ = undefined
