{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Optimize.Driver where

import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Located (Located (..))
import Data.Text (Text)
import Language.Zilch.CLI.Flags (Flags, debug, doDump, dumpANFOpt)
import Language.Zilch.Optimize.ArgumentTuplingAnalysis (tupleArguments)
import Language.Zilch.Pretty.ANF ()
import Language.Zilch.Typecheck.ANF (Module (..))
import Prettyprinter (pretty)

optimize :: (?buildProgress :: Bool, MonadIO m) => Flags -> [(FilePath, [Located Text], Located Module)] -> m (FilePath, [Located Text], Located Module)
optimize _ [] = undefined
optimize flags mods = do
  when ?buildProgress do
    liftIO $ putStrLn "Optimizing all modules…"

  let (path, name, mod) = gatherDefinitions mods

  (path', name', mod') <- pipeline (path, name, mod)

  liftIO $ doDumpANFOpt flags mod' path'
  pure (path', name', mod')
  where
    pipeline = tupleArguments flags

-- TODO: put this at the beginning of the codegen pipeline
--
-- check if building executable (i.e. @--no-main@ is not specified on the command line)
--   (,warns) . pure <$> liftEither (monomorphiseProgram mods)

gatherDefinitions :: [(FilePath, [Located Text], Located Module)] -> (FilePath, [Located Text], Located Module)
gatherDefinitions [] = undefined
gatherDefinitions [x] = x
gatherDefinitions ((path, modName, Module defs :@ p) : xs) =
  let (_, _, Module defs' :@ _) = gatherDefinitions xs
   in (path, modName, Module (defs <> defs') :@ p)

doDumpANFOpt :: Flags -> Located Module -> FilePath -> IO ()
doDumpANFOpt flags mod path = doDump flags "anf-opt" (dumpANFOpt . debug) (pretty mod) path
