module Language.Zilch.CLI.Flags where

import Data.Hashable (hash)
import System.Directory (createDirectoryIfMissing)
import System.FilePath (joinPath, splitPath, (<.>))

data Flags = Flags
  { debug :: DebugFlags,
    config :: ConfigFlags,
    input :: InputFlags,
    output :: OutputFlags,
    warnings :: WarningFlags
  }
  deriving (Show)

data DebugFlags = DebugFlags
  { -- | @-ddump-ast@
    dumpAST :: Bool,
    -- | @-ddump-tast@
    dumpTAST :: Bool,
    -- | @-ddump-anf@
    dumpANF :: Bool,
    -- | @-ddump-anf-opt@
    dumpANFOpt :: Bool,
    -- | @-ddump-dir=DIR@
    dumpDir :: Maybe FilePath,
    -- | @--build-progress@
    buildProgress :: Bool,
    -- | @-ddump-arities@
    dumpArities :: Bool
  }
  deriving (Show)

data ConfigFlags = ConfigFlags
  { -- | @-fcolor-diagnostics@ and @-fno-color-diagnostics@
    colorDiagnostics :: Bool
  }
  deriving (Show)

data InputFlags = InputFlags
  { -- | [FILE...]
    modules :: [FilePath],
    -- | @-I@
    includeDirs :: [FilePath]
  }
  deriving (Show)

data OutputFlags = OutputFlags
  { -- | @-o@ or @--out@
    out :: FilePath,
    -- | @--no-main@
    noMain :: Bool,
    -- | @--keep-zci@
    keepZci :: Bool,
    -- | @--keep-zco@
    keepZco :: Bool
  }
  deriving (Show)

data WarningFlags = WarningFlags
  { -- | @-Wunused-binding@ and @-Wno-unused-binding@
    unusedBinding :: Bool,
    -- | @-Wrec-non-rec@ and @-Wno-rec-non-rec@
    recNonRec :: Bool,
    -- | @-Wadditive-singleton@ and @-Wno-additive-singleton@
    additiveSingleton :: Bool,
    -- | @-Werror@
    areErrors :: Bool,
    -- | @-Wall@
    all :: Bool
  }
  deriving (Show)

getDumpBasePath :: Flags -> [FilePath]
getDumpBasePath flags = maybe [".zilch", "dump"] splitPath $ dumpDir (debug flags)

doDump :: Show a => Flags -> String -> (Flags -> Bool) -> a -> FilePath -> IO ()
doDump flags prefix p x path
  | p flags = do
      let dir = getDumpBasePath flags

      createDirectoryIfMissing True (joinPath dir)
      writeFile (joinPath $ dir <> [show (hash path) <> "-" <> prefix <.> "dbg" <.> "zc"]) (show x)
  | otherwise = pure ()

doDump' :: Show a => Flags -> String -> (Flags -> Bool) -> a -> IO ()
doDump' flags fileName p x
  | p flags = do
      let dir = getDumpBasePath flags

      createDirectoryIfMissing True (joinPath dir)
      writeFile (joinPath $ dir <> [fileName]) (show x)
  | otherwise = pure ()
