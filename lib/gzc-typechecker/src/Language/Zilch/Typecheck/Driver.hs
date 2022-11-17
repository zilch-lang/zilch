{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Driver (typecheckModules) where

import Control.Monad (when)
import Control.Monad.Except (MonadError, liftEither, runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Bifunctor (second)
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.Located (Located, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, def)
import Language.Zilch.CLI.Flags (WarningFlags)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import qualified Language.Zilch.Typecheck.IR as IR
import Language.Zilch.Typecheck.Imports (ImportCache)
import qualified Language.Zilch.Typecheck.Imports as Cache
import Language.Zilch.Typecheck.Internal.TAST2IR (translateModules)

-- import Language.Zilch.Typecheck.Monomorphiser (monomorphiseProgram)

type MonadDriver m = (MonadIO m, MonadError (Diagnostic String) m)

typecheckModules :: (?warnings :: WarningFlags, ?buildProgress :: Bool, ?noMain :: Bool, MonadIO m) => [(FilePath, [Located Text], Located AST.Module)] -> m (Either (Diagnostic String) ([(FilePath, [Located Text], Located IR.Module)], Diagnostic String))
typecheckModules mods = runExceptT $ do
  (mods, warns) <- typecheckModulesWithCache mempty mods

  when ?buildProgress do
    liftIO . putStrLn $ "Translating modules to internal IR…"
  let mods' = translateModules mods

  pure (mods', warns)

-- check if building executable (i.e. @--no-main@ is not specified on the command line)
-- if ?noMain
--   then pure (mods', warns)
--   else (,warns) . pure <$> liftEither (monomorphiseProgram mods')

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
