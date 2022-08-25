{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Driver (typecheckModules) where

import Data.Bifunctor (second)
import Data.Located (Located)
import Data.Text (Text)
import Error.Diagnose (Diagnostic, def)
import Language.Zilch.CLI.Flags (WarningFlags)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import Language.Zilch.Typecheck.Imports (ImportCache)
import qualified Language.Zilch.Typecheck.Imports as Cache

typecheckModules :: (?warnings :: WarningFlags) => [(FilePath, [Located Text], Located AST.Module)] -> Either (Diagnostic String) ([(FilePath, [Located Text], Located TAST.Module)], Diagnostic String)
typecheckModules = typecheckModulesWithCache mempty

typecheckModulesWithCache :: (?warnings :: WarningFlags) => ImportCache -> [(FilePath, [Located Text], Located AST.Module)] -> Either (Diagnostic String) ([(FilePath, [Located Text], Located TAST.Module)], Diagnostic String)
typecheckModulesWithCache _ [] = pure (mempty, def)
typecheckModulesWithCache cache ((path, mod, ast) : fs) = do
  (tast, interface, warns) <- elabProgram cache ast
  (mods, warns) <- second (warns <>) <$> typecheckModulesWithCache (Cache.insert (path, mod) interface cache) fs
  pure ((path, mod, tast) : mods, warns)
