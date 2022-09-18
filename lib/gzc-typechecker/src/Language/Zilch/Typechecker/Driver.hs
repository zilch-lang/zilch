{-# LANGUAGE ImplicitParams #-}

module Language.Zilch.Typechecker.Driver where

import Data.Located (Located)
import Data.Text (Text)
import Error.Diagnose (Diagnostic)
import Language.Zilch.CLI.Flags (WarningFlags)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Imports (ImportCache)

typecheckModules :: (?warnings :: WarningFlags) => [(FilePath, [Located Text], Located AST.Module)] -> Either (Diagnostic String) ([(FilePath, [Located Text], Located TAST.Module)], Diagnostic String)
typecheckModules = typecheckModulesWithCache mempty

typecheckModulesWithCache :: (?warnings :: WarningFlags) => ImportCache -> [(FilePath, [Located Text], Located AST.Module)] -> Either (Diagnostic String) ([(FilePath, [Located Text], Located TAST.Module)], Diagnostic String)
typecheckModulesWithCache _ [] = pure (mempty, def)
typecheckModulesWithCache cache ((path, mod, ast) : fs) = do
  (tast, warns) <- first mkDiagnostic $ elabProgram ast
  (mods, warns) <- second (warns <>) <$> typecheckModulesWithCache cache fs
  pure ((path, mod, tast) : mods, warns)

-- typecheckModulesWithCache cache ((path, mod, ast) : fs) = do
--   (tast, interface, warns) <- elabProgram ast
--   (mods, warns) <- second (warns <>) <$> typecheckModulesWithCache (Cache.insert (path, mod) interface cache) fs
--   pure ((path, mod, tast) : mods, warns)
