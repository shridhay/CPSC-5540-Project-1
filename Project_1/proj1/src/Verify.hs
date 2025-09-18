module Verify (Result(..), verify) where

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify _ = undefined
