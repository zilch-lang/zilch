{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Driver (typecheckModules) where

import Control.Monad (when)
import Control.Monad.Except (MonadError, runExceptT, liftEither)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Bifunctor (second)
import Data.List (intercalate)
import Data.Located (Located, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, def)
import Language.Zilch.CLI.Flags (WarningFlags)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import Language.Zilch.Typecheck.Imports (ImportCache)
import qualified Language.Zilch.Typecheck.Imports as Cache

type MonadDriver m = (MonadIO m, MonadError (Diagnostic String) m)

typecheckModules :: (?warnings :: WarningFlags, ?buildProgress :: Bool, MonadIO m) => [(FilePath, [Located Text], Located AST.Module)] -> m (Either (Diagnostic String) ([(FilePath, [Located Text], Located TAST.Module)], Diagnostic String))
typecheckModules = runExceptT . typecheckModulesWithCache mempty

typecheckModulesWithCache :: (?warnings :: WarningFlags, ?buildProgress :: Bool, MonadDriver m) => ImportCache -> [(FilePath, [Located Text], Located AST.Module)] -> m ([(FilePath, [Located Text], Located TAST.Module)], Diagnostic String)
typecheckModulesWithCache _ [] = pure (mempty, def)
typecheckModulesWithCache cache ((path, mod, ast) : fs) = do
  when ?buildProgress do
    liftIO . putStrLn $ "Type-checking module " <> mkMod mod <> " (" <> path <> ")…"

  (tast, interface, warns) <- liftEither $ elabProgram cache ast
  (mods, warns) <- second (warns <>) <$> typecheckModulesWithCache (Cache.insert (path, mod) interface cache) fs
  pure ((path, mod, tast) : mods, warns)
  where
    mkMod :: [Located Text] -> String
    mkMod = intercalate "::" . fmap (Text.unpack . unLoc)
