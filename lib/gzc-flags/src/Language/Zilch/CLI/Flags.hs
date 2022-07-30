module Language.Zilch.CLI.Flags where

data Flags = Flags
  { debug :: DebugFlags,
    config :: ConfigFlags,
    input :: InputFlags,
    output :: OutputFlags
  }
  deriving (Show)

data DebugFlags = DebugFlags
  { dumpAST :: Bool }
  deriving (Show)

instance Semigroup DebugFlags where
  f1 <> f2 =
    DebugFlags
      { dumpAST = dumpAST f1 || dumpAST f2
      }

instance Monoid DebugFlags where
  mempty =
    DebugFlags
      { dumpAST = False
      }

data ConfigFlags = ConfigFlags
  { -- | @-fcolor-diagnostics@ and @-fno-color-diagnostics@
    colorDiagnostics :: Bool
  }
  deriving (Show)

instance Semigroup ConfigFlags where
  f1 <> f2 =
    ConfigFlags
      { colorDiagnostics = colorDiagnostics f1 && colorDiagnostics f2
      }

instance Monoid ConfigFlags where
  mempty =
    ConfigFlags
      { colorDiagnostics = True
      }

data InputFlags = InputFlags
  { -- | [FILE...]
    files :: [FilePath]
  }
  deriving (Show)

instance Semigroup InputFlags where
  f1 <> f2 =
    InputFlags
      { files = files f1 <> files f2
      }

instance Monoid InputFlags where
  mempty =
    InputFlags
      { files = mempty
      }

data OutputFlags = OutputFlags
  { -- | @-o@ or @--out@
    out :: FilePath
  }
  deriving (Show)
