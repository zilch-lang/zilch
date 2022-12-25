module CLI.Flags where

data AllFlags
  = AllFlags
      InputFlags
      OutputFlags

data InputFlags
  = -- | The list of all flags related to inputs.
    InputFlags
      [FilePath]
      -- ^ The list of include directories.
      [String]
      -- ^ The list of input modules.

data OutputFlags
  = -- | The list of all flags related to outputs.
    OutputFlags
      FilePath
      -- ^ The binary output path.
