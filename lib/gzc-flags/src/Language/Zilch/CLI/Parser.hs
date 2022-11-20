{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.CLI.Parser (getFlags) where

import Control.Applicative ((<|>))
import Data.List (nub, partition)
import Language.Zilch.CLI.Flags
import Options.Applicative (Parser, action, argument, completeWith, customExecParser, eitherReader, fullDesc, help, helper, hidden, info, internal, long, many, metavar, option, prefs, short, showDefault, showHelpOnError, str, strOption, switch, value, (<**>))
import Prelude hiding (all)

getFlags :: IO Flags
getFlags = customExecParser preferences opts
  where
    opts = info (pCli <**> helper) (fullDesc)
    preferences = prefs showHelpOnError

---------------------------------------------------------------------------------

pCli :: Parser Flags
pCli = do
  output <- pOutput
  config <- pConfig
  debug <- pDebug
  warnings <- mkWarnings <$> many pWarning
  input <- pInput

  pure Flags {..}

pDebug :: Parser DebugFlags
pDebug = do
  ~(ast, tast, anf, anfopt, dir) <- go <$> many (option (eitherReader debug) (short 'd' <> help "Set various compiler debugging flags" <> metavar "FLAG" <> completeWith flagList))
  -- here we have to use an irrefutable (lazy) pattern
  -- otherwise GHC infers a @Monad m1@ constraint for the whole @do@ expression
  --
  -- see https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/applicative_do.html#strict-patterns
  buildProgress <- switch (long "build-progress" <> help "Turn on progress logging" <> internal)
  pure $ DebugFlags ast tast anf anfopt dir buildProgress
  where
    debug "dump-ast" = Right (True, False, False, False, Nothing)
    debug "dump-tast" = Right (False, True, False, False, Nothing)
    debug "dump-anf" = Right (False, False, True, False, Nothing)
    debug "dump-anf-opt" = Right (False, False, False, True, Nothing)
    debug "dump-dir=" = Left "dump-dir: Missing directory"
    debug "dump-dir" = Left "dump-dir: Missing directory"
    debug ('d' : 'u' : 'm' : 'p' : '-' : 'd' : 'i' : 'r' : '=' : dir) = Right (False, False, False, False, Just dir)
    debug spec = Left $ "Invalid command '" <> spec <> "'"

    go =
      foldr
        ( \(ast1, tast1, anf1, anfopt1, dir1) (ast2, tast2, anf2, anfopt2, dir2) ->
            (ast1 || ast2, tast1 || tast2, anf1 || anf2, anfopt1 || anfopt2, dir1 <|> dir2)
        )
        (False, False, False, False, Nothing)

    flagList =
      [ "dump-ast",
        "dump-tast",
        "dump-anf",
        "dump-anf-opt",
        "dump-dir"
      ]

pConfig :: Parser ConfigFlags
pConfig =
  ConfigFlags
    <$> option (eitherReader colorDiagnostics) (short 'f' <> value True <> help "Set compiler options" <> metavar "FLAG" <> completeWith flagList)
  where
    colorDiagnostics "color-diagnostics" = Right True
    colorDiagnostics "no-color-diagnostics" = Right False
    colorDiagnostics _ = Left ""

    flagList =
      [ "color-diagnostics",
        "no-color-diagnostics"
      ]

pInput :: Parser InputFlags
pInput = do
  includes <- many (strOption (short 'I' <> metavar "DIR" <> help "Add a path to the search path, where to find additional .zc and .zci files" <> action "directory"))
  mods <- many (argument str $ metavar "MODULES..." <> help "The list of module to compile" <> action "file")

  pure $ InputFlags mods includes

pOutput :: Parser OutputFlags
pOutput =
  OutputFlags
    <$> strOption (long "out" <> short 'o' <> metavar "FILE" <> value "a.out" <> help "Set the path to the output file" <> showDefault)
    <*> switch (long "no-main" <> help "Pass if the modules to be built do not contain a 'main' function")
    <*> switch (long "keep-zci" <> help "Preserve the .zci files in the dump directory")
    <*> switch (long "keep-zco" <> help "Preserve the .zco files in the dump directory")

--------------------------------

pWarning :: Parser Integer
pWarning = option (eitherReader warn) (short 'W' <> help "Choose which warning to enable/disable" <> metavar "[no-]WARN" <> completeWith flagList)
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

    flagList =
      [ "all",
        "error",
        "no-error",
        "unused-binding",
        "no-unused-binding",
        "rec-non-rec",
        "no-rec-non-rec",
        "additive-singleton",
        "no-additive-singleton"
      ]

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
