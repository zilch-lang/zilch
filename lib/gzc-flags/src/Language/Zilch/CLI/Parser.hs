{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.CLI.Parser (getFlags) where

import Control.Applicative ((<|>))
import Data.List (nub, partition)
import Language.Zilch.CLI.Flags
import Options.Applicative (Parser, argument, customExecParser, eitherReader, fullDesc, help, helper, hidden, info, long, many, metavar, option, prefs, short, showHelpOnError, str, strOption, switch, value, (<**>))
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
pDebug = do
  ~(ast, tast, dir) <- go <$> many (option (eitherReader debug) (short 'd' <> hidden))
  -- here we have to use an irrefutable (lazy) pattern
  -- otherwise GHC infers a @Monad m1@ constraint for the whole @do@ expression
  --
  -- see https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/applicative_do.html#strict-patterns
  buildProgress <- switch (long "build-progress" <> help "Turns on progress logging" <> hidden)
  pure $ DebugFlags ast tast dir buildProgress
  where
    debug "dump-ast" = Right (True, False, Nothing)
    debug "dump-tast" = Right (False, True, Nothing)
    debug "dump-dir=" = Left "dump-dir: Missing directory"
    debug "dump-dir" = Left "dump-dir: Missing directory"
    debug ('d' : 'u' : 'm' : 'p' : '-' : 'd' : 'i' : 'r' : '=' : dir) = Right (False, False, Just dir)
    debug spec = Left $ "Invalid command '" <> spec <> "'"

    go = foldr (\(ast1, tast1, dir1) (ast2, tast2, dir2) -> (ast1 || ast2, tast1 || tast2, dir1 <|> dir2)) (False, False, Nothing)

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
    <$> many (argument str $ metavar "MODULES...")
    <*> many (strOption (short 'I' <> metavar "DIR" <> help "Adds a path to the search path, where to find .zc and .zci files"))

pOutput :: Parser OutputFlags
pOutput =
  OutputFlags
    <$> strOption (long "out" <> short 'o' <> metavar "FILE" <> value "a.out" <> help "Sets the path to the output file")
    <*> switch (long "no-main" <> help "Pass if the modules we are building do not contain a 'main' function")
    <*> switch (long "keep-zci" <> help "Preserve the .zci files in the dump directory")
    <*> switch (long "keep-zco" <> help "Preserve the .zco files in the dump directory")

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
      let ws' =
            ws
              { all = i == 0 || all ws,
                areErrors = i == 1 || areErrors ws,
                unusedBinding = i == 0 || i == 2 || all ws || unusedBinding ws,
                recNonRec = i == 0 || i == 3 || all ws || recNonRec ws,
                additiveSingleton = i == 0 || i == 4 || all ws || additiveSingleton ws
              }
       in go ws' is

    go' ws [] = ws
    go' ws (i : is) =
      let ws' =
            ws
              { areErrors = if i == -1 then False else areErrors ws,
                unusedBinding = if i == -2 then False else unusedBinding ws,
                recNonRec = if i == -3 then False else recNonRec ws,
                additiveSingleton = if i == -4 then False else additiveSingleton ws
              }
       in go' ws' is
