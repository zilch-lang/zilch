{-# LANGUAGE OverloadedLists #-}

module Driver where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text (Text)
import Language.Zilch.Syntax.ModuleResolver (parseAndResolveModules)
import Text.Diagnose (printDiagnostic, Diagnostic, (<~<))
import System.IO (stderr)
import System.Exit (exitFailure)
import Data.List (foldl')
import Language.Zilch.Syntax.Desugarer (runDesugarer)

-- | Runs the compiler on the module given.
runGZC :: MonadIO m => Text -> m ()
runGZC mod = do
  let ?includePath = ["."]

  (result, (fileContents, parsedModules, topsort)) <- parseAndResolveModules mod

  case result of
    Left d -> liftIO do
      printDiagnostic True stderr (d <~~< fileContents)
      exitFailure
    Right _ -> pure ()

  case runDesugarer topsort parsedModules of
    Left d -> liftIO do
      printDiagnostic True stderr (d <~~< fileContents)
      exitFailure
    Right _ -> pure ()

  pure ()


(<~~<) :: Diagnostic s m a -> [(String, [s a])] -> Diagnostic s m a
(<~~<) = foldl' (<~<)
