module Main where

import qualified Bank

main :: IO ()
main = Bank.runExample >>= print
