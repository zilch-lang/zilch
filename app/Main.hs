{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import qualified EntryPoint
import System.Environment (getArgs)
import Control.Monad (forM_)
import Error.Diagnose.Diagnostic (printDiagnostic)
import Error.Diagnose.Style (defaultStyle)
import System.IO (stderr)

main :: IO ()
main = do
  files <- getArgs
  forM_ files \f -> do
    EntryPoint.entry_point f >>= \case
      Left d -> printDiagnostic stderr True True 4 defaultStyle d
      Right cst -> putStrLn "✅ OK!"

