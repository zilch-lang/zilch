{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BinaryLiterals #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.CLI.Parser (getFlags) where

import Data.List (nub, partition)
import Language.Zilch.CLI.Flags
import Options.Applicative (Parser, argument, customExecParser, eitherReader, fullDesc, help, helper, hidden, info, long, many, metavar, option, prefs, short, showHelpOnError, str, strOption, value, (<**>))
import Prelude hiding (all)

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
  warnings <- mkWarnings <$> many pWarning

  pure Flags {..}

pDebug :: Parser DebugFlags
pDebug =
  DebugFlags
    <$> option (eitherReader dumpAST) (short 'd' <> value False <> hidden)
    <*> option (eitherReader dumpTAST) (short 'd' <> value False <> hidden)
    <*> option (eitherReader dumpDir) (short 'd' <> value Nothing <> hidden)
  where
    dumpAST "dump-ast" = Right True
    dumpAST _ = Left ""

    dumpTAST "dump-tast" = Right True
    dumpTAST _ = Left ""

    dumpDir "dump-dir=" = Left "Missing directory"
    dumpDir ('d' : 'u' : 'm' : 'p' : '-' : 'd' : 'i' : 'r' : '=' : dir) = Right $ Just dir
    dumpDir "dump-dir" = Right Nothing
    dumpDir _ = Left ""

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

--------------------------------

pWarning :: Parser Integer
pWarning = option (eitherReader warn) (short 'W' <> hidden)
  where
    warn "all" = Right 0
    warn "error" = Right 1
    warn "no-error" = Right (-1)
    warn "unused-binding" = Right 2
    warn "no-unused-binding" = Right (-2)
    warn "rec-non-rec" = Right 3
    warn "no-rec-non-rec" = Right (-3)
    warn "additive-singleton" = Right 4
    warn "no-additive-singleton" = Right (-4)
    warn other = Left $ "Unrecognized warning '" <> other <> "'"

mkWarnings :: [Integer] -> WarningFlags
mkWarnings indices =
  let (positive, negative) = partition (>= 0) $ nub indices
   in go' (go init positive) negative
  where
    init = WarningFlags False False False False False

    go ws [] = ws
    go ws (i : is) =
      let ws' = ws {
              all = i == 0 || all ws,
              areErrors = i == 1 || areErrors ws,
              unusedBinding = i == 0 || i == 2 || all ws || unusedBinding ws,
              recNonRec = i == 0 || i == 3 || all ws || recNonRec ws,
              additiveSingleton = i == 0 || i == 4 || all ws || additiveSingleton ws
            }
       in go ws' is

    go' ws [] = ws
    go' ws (i : is) =
      let ws' = ws {
              areErrors = if i == -1 then False else areErrors ws,
              unusedBinding = if i == -2 then False else unusedBinding ws,
              recNonRec = if i == -3 then False else recNonRec ws,
              additiveSingleton = if i == -4 then False else additiveSingleton ws
            }
      in go' ws' is
