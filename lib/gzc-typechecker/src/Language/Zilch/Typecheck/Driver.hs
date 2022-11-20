{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Driver (typecheckModules) where

import Control.Monad (forM_, when)
import Control.Monad.Except (MonadError, liftEither, runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Bifunctor (second)
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.Located (Located, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, def)
import Language.Zilch.CLI.Flags (Flags, WarningFlags, debug, doDump, dumpANF, dumpTAST)
import Language.Zilch.Pretty.ANF ()
import Language.Zilch.Pretty.TAST ()
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.ANF as ANF
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import Language.Zilch.Typecheck.Imports (ImportCache)
import qualified Language.Zilch.Typecheck.Imports as Cache
import Language.Zilch.Typecheck.Internal.IR2ANF (normalizeModule)
import Language.Zilch.Typecheck.Internal.TAST2IR (translateModules)
import Prettyprinter (pretty)

-- import Language.Zilch.Typecheck.Monomorphiser (monomorphiseProgram)

type MonadDriver m = (MonadIO m, MonadError (Diagnostic String) m)

typecheckModules :: (?warnings :: WarningFlags, ?buildProgress :: Bool, MonadIO m) => Flags -> [(FilePath, [Located Text], Located AST.Module)] -> m (Either (Diagnostic String) ([(FilePath, [Located Text], Located ANF.Module)], Diagnostic String))
typecheckModules flags mods = runExceptT $ do
  (mods, warns) <- typecheckModulesWithCache flags mempty mods

  when ?buildProgress do
    liftIO . putStrLn $ "Translating modules to A-normal form…"
  let mods' = translateModules mods <&> \(path, name, mod) -> (path, name, normalizeModule mod)

  forM_ mods' \(path, _, mod) ->
    liftIO $ doDumpANF flags mod path
  pure (mods', warns)

typecheckModulesWithCache :: (?warnings :: WarningFlags, ?buildProgress :: Bool, MonadDriver m) => Flags -> ImportCache -> [(FilePath, [Located Text], Located AST.Module)] -> m ([(FilePath, [Located Text], Located TAST.Module)], Diagnostic String)
typecheckModulesWithCache _ _ [] = pure (mempty, def)
typecheckModulesWithCache flags cache ((path, mod, ast) : fs) = do
  when ?buildProgress do
    liftIO . putStrLn $ "Type-checking module " <> mkMod mod <> " (" <> path <> ")…"

  (tast, interface, warns) <- liftEither $ elabProgram cache ast
  liftIO $ doDumpTAST flags tast path

  (mods, warns) <- second (warns <>) <$> typecheckModulesWithCache flags (Cache.insert (path, mod) interface cache) fs
  pure ((path, mod, tast) : mods, warns)
  where
    mkMod :: [Located Text] -> String
    mkMod = intercalate "::" . fmap (Text.unpack . unLoc)

doDumpTAST :: Flags -> Located TAST.Module -> FilePath -> IO ()
doDumpTAST flags mod = doDump flags "tast" (dumpTAST . debug) (pretty mod)

doDumpANF :: Flags -> Located ANF.Module -> FilePath -> IO ()
doDumpANF flags mod = doDump flags "anf" (dumpANF . debug) (pretty mod)
