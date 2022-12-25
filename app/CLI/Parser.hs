{-# LANGUAGE ApplicativeDo #-}

module CLI.Parser where

import CLI.Flags
import Data.Foldable (fold)
import Options.Applicative (Parser, customExecParser, fullDesc, helper, info, long, many, metavar, prefs, short, showDefault, showHelpOnError, strArgument, strOption, value)

getFlags :: IO AllFlags
getFlags = customExecParser preferences $ info (helper <*> cli) opts
  where
    opts = fold [fullDesc]

    preferences = prefs showHelpOnError

--------------------------------------------------------------------------

cli :: Parser AllFlags
cli = do
  output <- parseOutputFlags
  input <- parseInputFlags

  pure $ AllFlags input output

--------------------------------------------------------------------------

parseOutputFlags :: Parser OutputFlags
parseOutputFlags = do
  out <- strOption $ fold [short 'o', long "out", value "a.out", metavar "FILE", showDefault]

  pure $ OutputFlags out

parseInputFlags :: Parser InputFlags
parseInputFlags = do
  idirs <- many . strOption $ fold [short 'I', long "include", metavar "DIR"]
  mods <- many . strArgument $ fold [metavar "FILES..."]

  pure $ InputFlags idirs mods
