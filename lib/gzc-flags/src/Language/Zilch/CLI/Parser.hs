{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.CLI.Parser (getFlags) where

import Language.Zilch.CLI.Flags hiding (hidden)
import Options.Applicative (Parser, argument, customExecParser, eitherReader, flag, fullDesc, help, helper, hidden, info, long, many, metavar, option, prefs, short, showHelpOnError, str, strOption, value, (<**>))

getFlags :: IO Flags
getFlags = customExecParser preferences opts
  where
    opts = info (pCli <**> helper) (fullDesc)
    preferences = prefs showHelpOnError

---------------------------------------------------------------------------------

pCli :: Parser Flags
pCli = do
  debug <- pDebug
  config <- pConfig
  output <- pOutput
  input <- pInput

  pure Flags {..}

pDebug :: Parser DebugFlags
pDebug =
  DebugFlags
    <$> option (eitherReader dumpAST) (short 'd' <> value False <> hidden)
  where
    dumpAST "dump-ast" = Right True
    dumpAST _ = Left ""

pConfig :: Parser ConfigFlags
pConfig =
  ConfigFlags
    <$> option (eitherReader colorDiagnostics) (short 'f' <> value True <> hidden)
  where
    colorDiagnostics "color-diagnostics" = Right True
    colorDiagnostics "no-color-diagnostics" = Right False
    colorDiagnostics _ = Left ""

pInput :: Parser InputFlags
pInput =
  InputFlags
    <$> many (argument str $ metavar "FILES...")

pOutput :: Parser OutputFlags
pOutput =
  OutputFlags
    <$> strOption (long "out" <> short 'o' <> metavar "FILE" <> value "a.out" <> help "Sets the path to the output file")
