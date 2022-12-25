module Main where

import CLI.Parser (getFlags)
import EntryPoint (entrypoint)

main :: IO ()
main = getFlags >>= entrypoint
