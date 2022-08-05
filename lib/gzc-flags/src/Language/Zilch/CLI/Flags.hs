module Language.Zilch.CLI.Flags where

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
    -- | @-ddump-dir=DIR@
    dumpDir :: Maybe FilePath
  }
  deriving (Show)

data ConfigFlags = ConfigFlags
  { -- | @-fcolor-diagnostics@ and @-fno-color-diagnostics@
    colorDiagnostics :: Bool
  }
  deriving (Show)

data InputFlags = InputFlags
  { -- | [FILE...]
    files :: [FilePath]
  }
  deriving (Show)

data OutputFlags = OutputFlags
  { -- | @-o@ or @--out@
    out :: FilePath
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

