{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-@ LIQUID "--max-case-expand=0" @-}

module Syntax.Lexer (runLexer, runLexer') where

import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.Char (isSpace)
import Data.Foldable (foldl')
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, addReport, def)
import Error.Diagnose.Compat.Megaparsec (errorDiagnosticFromBundle)
import Located (Located (..), Position (..))
import Syntax.Errors
import Syntax.Tokens (Token (..))
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as MPL

-- | The monad representing the lexer is able to:
--
--   * Produce and accumulate any number of warnings;
--
--   * Fail whenever needed, e.g. on erroneous inputs (most likely impossible corner cases);
--
--   * Act like a monadic parser.
type MonadLexer m = (MonadWriter [LexicalWarning] m, MP.MonadParsec LexicalError Text m, MonadFail m)

{-@ ignore located @-}
-- | Transform a simple parser producing a value into a parser returning a located value.
located :: forall m a. MonadLexer m => m a -> m (Located a)
located p = do
  MP.SourcePos file beginLine beginColumn <- MP.getSourcePos
  res <- p
  MP.SourcePos _ endLine endColumn <- MP.getSourcePos

  let pos =
        Position
          (MP.unPos beginLine, MP.unPos beginColumn)
          (MP.unPos endLine, MP.unPos endColumn)
          file

  pure $ res :@ pos

{-@ ignore space @-}
-- | Convenient wrapper around 'MPL.space' to only skip multiple consecutive whitespaces (but no comment).
space :: MonadLexer m => m ()
space = MPL.space MPC.space1 MP.empty MP.empty

{-@ ignore lexeme @-}
-- | 'MPL.lexeme' but with its first argument set to 'space'.
lexeme :: MonadLexer m => m a -> m a
lexeme = MPL.lexeme space

-- -- | 'MPL.symbol' but with its first argument set to 'space'.
-- symbol :: MonadLexer m => Text -> m Text
-- symbol = MPL.symbol space

{-@ ignore eof @-}
-- | Parse and return a 'TkEOF' if at the end of the stream.
eof :: MonadLexer m => m (Located Token)
eof = located $ TkEOF <$ MP.eof

-------------------------------------------------------------------------------------

{-@ ignore runLexer' @-}
-- | A variant of 'runLexer' that works on a 'String' rather than a 'Text'.
runLexer' :: FilePath -> String -> Either (Diagnostic String) ([Located Token], Diagnostic String)
runLexer' path content = runLexer path (Text.pack content)

{-@ ignore runLexer @-}
-- | Run the lexer on the given file path and content.
--
-- Returns either an error as a 'Diagnostic', or a list of token and warnings as a 'Diagnostic'.
runLexer :: FilePath -> Text -> Either (Diagnostic String) ([Located Token], Diagnostic String)
runLexer path content =
  bimap
    (errorDiagnosticFromBundle Nothing "Lexical error on input" Nothing)
    (second toDiagnostic)
    $ MP.runParser (runWriterT entrypoint) path content
  where
    toDiagnostic warns = foldl' addReport def (fromLexicalWarning <$> warns)

-------------------------------------------------------------------------------------

{-@ ignore entrypoint @-}
-- | Parse any number of tokens in the whole file, until EOF.
entrypoint :: forall m. MonadLexer m => m [Located Token]
entrypoint = ignoreLeadingSpaces *> (concat' <$> MP.manyTill_ (lexeme token) eof)
  where
    ignoreLeadingSpaces = lexeme (pure ())

    concat' (xs, x) = xs <> [x]

    token =
      MP.choice
        [ lineComment,
          docComment,
          multilineComment,
          integer,
          identifierOrKeyword
        ]

-------------------------------------------------------------------------------------
-- Comments

{-@ ignore lineComment @-}
-- | Parse a line comment, starting with @--@ and expanding until the end of the line.
lineComment :: forall m. MonadLexer m => m (Located Token)
lineComment = located do
  _ <- MP.hidden $ MPC.string "--"
  front <- MP.takeWhileP Nothing (== '-')
  back <-
    MP.choice
      [ "" <$ MP.eof,
        "" <$ MPC.eol,
        do
          spc <- MP.satisfy isHSpace
          back <- Text.pack <$> MP.manyTill MP.anySingle MPC.eol
          pure (Text.singleton spc <> back)
      ]
  pure $ TkInlineComment (front <> back)

{-@ ignore docComment @-}
-- | Parse a documentation comment, which starts with @/--@ and ends with @-/@.
docComment :: forall m. MonadLexer m => m (Located Token)
docComment = specialMultilineComment "/--" "-/" TkDocComment

{-@ ignore multilineComment @-}
-- | Parse a multiline comment, which starts with @/-@ and ends with @-/@.
multilineComment :: forall m. MonadLexer m => m (Located Token)
multilineComment = specialMultilineComment "/-" "-/" TkMultilineComment

{-@ ignore specialMultilineComment @-}
-- | To avoid redundancy between 'docComment' and 'multilineComment'.
specialMultilineComment :: forall m. MonadLexer m => Text -> Text -> (Text -> Token) -> m (Located Token)
specialMultilineComment begin end tok = located do
  _ <- MP.hidden $ MPC.string begin
  body <- MP.manyTill anyOrNestedComment (MPC.string end)
  pure . tok $ mconcat body
  where
    anyOrNestedComment =
      MP.choice
        [ multilineComment >>= \case
            TkMultilineComment txt :@ _ -> pure $ "/-" <> txt <> "-/"
            tk :@ _ -> fail $ "Impossible token " <> show tk <> " while parsing nested comment",
          Text.singleton <$> MP.anySingle
        ]

--------------------------------------------------------------------------------------
-- Numbers

{-@ ignore integer @-}
integer :: forall m. MonadLexer m => m (Located Token)
integer = MP.label "a number" . located $ MP.choice [toNumber hexadecimal, toNumber octal, toNumber binary, decimalWithSuffix]
  where
    toNumber :: forall m. MonadLexer m => m Text -> m Token
    toNumber = fmap $ flip TkNumber Nothing

    hexadecimal = (<>) <$> MPC.string' "0x" <*> (Text.pack <$> MP.some hexDigit)
    hexDigit = MP.oneOf ("0123456789ABCDEFabcdef" :: String)

    octal = MP.empty

    binary = MP.empty

    decimal = Text.pack <$> MP.some decDigit
    decDigit = MP.oneOf ("0123456789" :: String)

    decimalWithSuffix = do
      nb <- decimal
      ty <-
        MP.optional . MP.try $
          identifierOrKeyword >>= \case
            TkSymbol suffix :@ _ -> pure suffix
            _ :@ _ -> MP.empty
      pure $ TkNumber nb ty

--------------------------------------------------------------------------------------
-- Identifiers & keywords

{-@ ignore identifierOrKeyword @-}
identifierOrKeyword :: forall m. MonadLexer m => m (Located Token)
identifierOrKeyword = reservedSymbol MP.<|> anySymbol

{-@ ignore reservedSymbol @-}
reservedSymbol :: forall m. MonadLexer m => m (Located Token)
reservedSymbol =
  located $
    MP.choice
      [ TkDoubleLeftBrace <$ MPC.string "{{",
        TkDoubleRightBrace <$ MPC.string "}}",
        TkLeftBrace <$ MPC.string "{",
        TkRightBrace <$ MPC.string "}",
        TkUniDoubleLeftBrace <$ MPC.string "⦃",
        TkUniDoubleRightBrace <$ MPC.string "⦄",
        TkLeftParen <$ MPC.string "(",
        TkRightParen <$ MPC.string ")",
        TkDoubleColon <$ MPC.string "::",
        TkUniDoubleColon <$ MPC.string "∷",
        TkColonEquals <$ MPC.string ":=",
        TkUniColonEquals <$ MPC.string "≔",
        TkColon <$ MPC.string ":",
        TkLeftAngle <$ MPC.string "⟨",
        TkRightAngle <$ MPC.string "⟩",
        TkComma <$ MPC.string ",",
        TkAt <$ MPC.string "@"
      ]

{-@ ignore anySymbol @-}
anySymbol :: forall m. MonadLexer m => m (Located Token)
anySymbol = located $ toToken <$> MP.some (MP.noneOf (":,{}()⦃⦄⟨⟩ \t\n\r\v∷@" :: String))
  where
    toToken "->" = TkRightArrow
    toToken "→" = TkUniRightArrow
    toToken "=>" = TkDoubleRightArrow
    toToken "⇒" = TkUniDoubleRightArrow
    toToken "×" = TkTimes
    toToken "⊗" = TkUniTensor
    toToken "&" = TkAmpersand
    toToken "let" = TkLet
    toToken "rec" = TkRec
    toToken "val" = TkVal
    toToken "public" = TkPublic
    toToken "enum" = TkEnum
    toToken "record" = TkRecord
    toToken "import" = TkImport
    toToken "open" = TkOpen
    toToken "as" = TkAs
    toToken "lam" = TkLam
    toToken "λ" = TkUniLam
    toToken "do" = TkDo
    toToken "_" = TkUnderscore
    toToken "type" = TkType
    toToken "assume" = TkAssume
    toToken "true" = TkTrue
    toToken "false" = TkFalse
    toToken "if" = TkIf
    toToken "then" = TkThen
    toToken "else" = TkElse
    toToken "mutual" = TkMutual
    toToken "#attributes" = TkHashAttributes
    toToken s = TkSymbol (Text.pack s)

--------------------------------------------------------------------------------------
-- Misc

-- | Is it a horizontal space character?
isHSpace :: Char -> Bool
isHSpace x = isSpace x && x /= '\n' && x /= '\r'
