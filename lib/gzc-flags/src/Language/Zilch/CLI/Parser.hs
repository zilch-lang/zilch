{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.CLI.Parser (getFlags) where

import Control.Applicative ((<|>))
import Data.List (intercalate, nub, partition)
import Language.Zilch.CLI.Flags
import Options.Applicative (ParseError (..), Parser, action, argument, completeWith, customExecParser, eitherReader, fullDesc, help, helper, hidden, info, internal, long, many, metavar, noArgError, option, prefs, readerAbort, short, showDefault, showHelpOnError, str, strOption, switch, value, (<**>))
import Options.Applicative.Types (readerAsk)
import Prelude hiding (all)

getFlags :: IO Flags
getFlags = customExecParser preferences opts
  where
    opts = info (pCli <**> helper <**> man) (fullDesc)
    preferences = prefs showHelpOnError

---------------------------------------------------------------------------------

man :: Parser (a -> a)
man =
  option manReader $
    mconcat
      [ value id,
        long "man",
        metavar "[FLAG]",
        noArgError (InfoMsg fullMan),
        help "Show help about the command line flag FLAG (such as \"-d\"). FLAG is a comma-separated list of flags. If FLAG is unspecified or empty, show help for all the command line flags",
        hidden
      ]
  where
    manReader = do
      flag <- readerAsk
      readerAbort $ InfoMsg case filter (not . null) $ splitOn ',' flag of
        [] -> fullMan
        flags -> intercalate "\n\n" [manEntry f | f <- flags]

    fullMan :: String
    fullMan =
      "Manual entries for all flags:\n"
        <> intercalate "\n\n" [entryText f | f <- allFlags]

    manEntry flag
      | flag `elem` allFlags = entryHeader flag <> "\n" <> entryText flag
      | otherwise = "Option \"" <> flag <> "\" unknown. Check --help or --man for a list of supported options."

    entryHeader flag = "Manual entry for flag \"" <> flag <> "\":"

    splitOn _ "" = []
    splitOn c str = case break (== c) str of
      (prefix, "") -> [prefix]
      (prefix, _ : suffix) -> prefix : splitOn c suffix

    entryText :: String -> String
    entryText "-d" =
      "  -d FLAG: Turn on various compiler debugging flags.\n\
      \           These options are meant to be used to create dumps when reporting bugs.\n\
      \           An exhaustive list is given underneath, along with simple explanations.\n\
      \\n\
      \     dump-dir=DIR:\n\
      \         Set the dumping directory to DIR.\n\
      \         The default value for DIR is \"./.zilch/dump\".\n\
      \     dump-ast:\n\
      \         Dump the pretty-printed AST (after parsing and desugaring) to \"DIR/<hash>-ast.dbg.zc\".\n\
      \     dump-tast:\n\
      \         Dump a pretty-printed version of the typed AST, that is the AST with all type information filled.\n\
      \         This may be a bit unreadable at times.\n\
      \         The typed AST is dumped to \"DIR/<hash>-tast.dbg.zc\".\n\
      \     dump-anf:\n\
      \         Dump the A-normal form of each module to \"DIR/<hash>-anf.dbg.zc\".\n\
      \     dump-anf-opt:\n\
      \         Dump the optimized A-normal form where all modules are merged into one.\n\
      \         This flag will be ignored if \"--no-main\" is specified.\n\
      \         The optimized A-normal form is dumped to the file \"DIR/<hash>-anf-opt.dbg.zc\"."
    entryText "-f" =
      "  -f FLAG: Control various compiler options.\n\
      \           FLAG is one of the following:\n\
      \\n\
      \     [no-]color-diagnostics:\n\
      \         Turn on or off colors when in the error reports.\n\
      \         Colors are on by default, but this may not suit some operating systems."
    entryText "-W" =
      "  -W [no-]WARN: Turn on/off specific warnings (or most of them).\n\
      \                To turn on a warning, simply specify \"-W WARN\".\n\
      \                To turn it off, specify \"-W no-WARN\".\n\
      \                Negation has priority over anything else, no matter the order, meaning that if both\n\
      \                \"-W X\" and \"-W no-X\" are specified then the warning \"X\" will not be raised.\n\
      \                WARN is one of the following:\n\
      \\n\
      \     unused-binding:\n\
      \         Throw a warning when an unrestricted binding has not been used.\n\
      \         Consider the following example:\n\
      \             let f() := 25\n\
      \             public let g() := ()\n\
      \         \"f\" is not public and has not been used within the module, therefore a warning should be raised.\n\
      \     rec-non-rec:\n\
      \         Raise a warning when a binding declared with \"rec\" hasn't been used recursively\n\
      \         (thus can be transformed into a normal non-recursive binding).\n\
      \     additive-singleton:\n\
      \         This warning stems from the fact that \"⟨x⟩\" is strictly equivalent to \"x\".\n\
      \         This means that the extra pair of angles can be avoided.\n\
      \         The same does not hold for \"(x)\", hence the name of the warning.\n\
      \     all:\n\
      \         This option cannot be negated (there is no \"no-all\" counterpart).\n\
      \         Turn on all the non-harming warnings, such as \"unused-binding\", \"rec-non-rec\", \"additive-singleton\".\n\
      \     error:\n\
      \         Treat all warnings as errors.\n\
      \         If this is unwanted, pass \"-W no-error\" to the command-line."
    entryText _ = "Ohhhhh, you found me! Great job. :) But this shouldn't happen..."

    allFlags = ["-d", "-f", "-W"]

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
  ~(ast, tast, anf, anfopt, arities, dir) <-
    go
      <$> many
        ( option
            (eitherReader debug)
            ( short 'd'
                <> help "Set various compiler debugging flags"
                <> metavar "FLAG"
                <> completeWith flagList
                <> hidden
            )
        )
  -- here we have to use an irrefutable (lazy) pattern
  -- otherwise GHC infers a @Monad m1@ constraint for the whole @do@ expression
  --
  -- see https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/applicative_do.html#strict-patterns
  buildProgress <- switch (long "build-progress" <> help "Turn on progress logging" <> internal)
  pure $ DebugFlags ast tast anf anfopt dir buildProgress arities
  where
    debug "dump-ast" = Right (True, False, False, False, False, Nothing)
    debug "dump-tast" = Right (False, True, False, False, False, Nothing)
    debug "dump-anf" = Right (False, False, True, False, False, Nothing)
    debug "dump-anf-opt" = Right (False, False, False, True, False, Nothing)
    debug "dump-arities" = Right (False, False, False, False, True, Nothing)
    debug "dump-dir=" = Left "dump-dir: Missing directory"
    debug "dump-dir" = Left "dump-dir: Missing directory"
    debug ('d' : 'u' : 'm' : 'p' : '-' : 'd' : 'i' : 'r' : '=' : dir) = Right (False, False, False, False, False, Just dir)
    debug spec = Left $ "Invalid command '" <> spec <> "'"

    go =
      foldr
        ( \(ast1, tast1, anf1, anfopt1, arities1, dir1) (ast2, tast2, anf2, anfopt2, arities2, dir2) ->
            (ast1 || ast2, tast1 || tast2, anf1 || anf2, anfopt1 || anfopt2, arities1 || arities2, dir1 <|> dir2)
        )
        (False, False, False, False, False, Nothing)

    flagList =
      [ "dump-ast",
        "dump-tast",
        "dump-anf",
        "dump-anf-opt",
        "dump-arities",
        "dump-dir"
      ]

pConfig :: Parser ConfigFlags
pConfig =
  ConfigFlags
    <$> option
      (eitherReader colorDiagnostics)
      ( short 'f'
          <> value True
          <> help "Set compiler options"
          <> metavar "FLAG"
          <> completeWith flagList
          <> hidden
      )
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
  includes <-
    many
      ( strOption
          ( short 'I'
              <> metavar "DIR"
              <> help "Add a path to the search path, where to find additional .zc and .zci files"
              <> action "directory"
          )
      )
  mods <- many (argument str $ metavar "MODULES..." <> help "The list of module to compile" <> action "file")

  pure $ InputFlags mods includes

pOutput :: Parser OutputFlags
pOutput =
  OutputFlags
    <$> strOption
      ( long "out"
          <> short 'o'
          <> metavar "FILE"
          <> value "a.out"
          <> help "Set the path to the output file"
          <> showDefault
          <> action "file"
      )
    <*> switch
      ( long "no-main"
          <> help "Pass if the modules to be built do not contain a 'main' function"
      )
    <*> switch
      ( long "keep-zci"
          <> help "Preserve the .zci files in the dump directory"
          <> hidden
      )
    <*> switch
      ( long "keep-zco"
          <> help "Preserve the .zco files in the dump directory"
          <> hidden
      )

--------------------------------

pWarning :: Parser Integer
pWarning =
  option
    (eitherReader warn)
    ( short 'W'
        <> help "Choose which warning to enable/disable"
        <> metavar "[no-]WARN"
        <> completeWith flagList
        <> hidden
    )
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
