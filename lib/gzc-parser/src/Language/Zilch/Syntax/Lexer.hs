{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Zilch.Syntax.Lexer where

import Control.Applicative ((<|>))
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.Foldable (foldl')
import Data.Located (Located)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, addReport, def)
import Error.Diagnose.Compat.Megaparsec
import Language.Zilch.Syntax.Core (Token (..))
import Language.Zilch.Syntax.Errors (LexicalError, LexicalWarning, fromLexicalWarning)
import Language.Zilch.Syntax.Internal (located)
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as MPL

type MonadLexer m = (MonadWriter [LexicalWarning] m, MP.MonadParsec LexicalError Text m)

space :: MonadLexer m => m ()
space = MPL.space MPC.space1 MP.empty MP.empty

lexeme :: MonadLexer m => m a -> m a
lexeme = MPL.lexeme space

symbol :: MonadLexer m => Text -> m Text
symbol = MPL.symbol space

-------------------------------------------------------------------

lexFile :: FilePath -> Text -> Either (Diagnostic String) ([Located Token], Diagnostic String)
lexFile fileName content =
  bimap
    (errorDiagnosticFromBundle "Lexical error on input" Nothing)
    (second toDiagnostic)
    $ MP.runParser (runWriterT lexProgram) fileName content
  where
    toDiagnostic warns = foldl' addReport def (fromLexicalWarning <$> warns)

lexProgram :: forall m. MonadLexer m => m [Located Token]
lexProgram = removeFrontSpace *> ((<>) <$> MP.many (lexeme token) <*> (pure <$> eof))
  where
    removeFrontSpace = lexeme (pure ())

token :: forall m. MonadLexer m => m (Located Token)
token = MP.choice ([MP.try character, comment, number, identifierOrReserved] :: [m (Located Token)])

eof :: MonadLexer m => m (Located Token)
eof = located (TkEOF <$ MP.eof)

character :: forall m. MonadLexer m => m (Located Token)
character =
  lexeme $
    located $
      TkCharacter . addQuotes <$> do
        MPC.char '\'' *> escapedChar <* MPC.char '\''
  where
    addQuotes = Text.cons '\'' . flip Text.snoc '\''

escapedChar :: forall m. MonadLexer m => m Text
escapedChar =
  lexeme $
    MP.choice
      ( [ (<>) <$> MPC.string "\\" <*> (Text.pack . pure <$> MP.oneOf ("nrvt\\'\"0ab" :: String)),
          Text.pack . pure <$> MP.anySingle
        ] ::
          [m Text]
      )

comment :: forall m. MonadLexer m => m (Located Token)
comment = lexeme $ located $ inlineComment <|> multilineComment
  where
    inlineComment, multilineComment :: m Token
    inlineComment = TkInlineComment <$> (MPC.string "--" *> MP.takeWhileP Nothing (/= '\n') <* (() <$ MPC.eol <|> MP.eof))
    multilineComment = TkMultilineComment . Text.pack <$> (MPC.string "/-" *> MP.manyTill MP.anySingle (MPC.string "-/"))

identifierOrReserved :: forall m. MonadLexer m => m (Located Token)
identifierOrReserved =
  lexeme $
    located $
      MP.choice
        ( [ TkDoubleLeftBrace <$ MPC.string "{{",
            TkUniDoubleLeftBrace <$ MPC.string "⦃",
            TkDoubleRightBrace <$ MPC.string "}}",
            TkUniDoubleRightBrace <$ MPC.string "⦄",
            TkDoubleColon <$ MPC.string "::",
            TkUniDoubleColon <$ MPC.string "∷",
            TkLeftParen <$ MPC.string "(",
            TkRightParen <$ MPC.string ")",
            TkColonEquals <$ MPC.string ":=",
            TkLeftBrace <$ MPC.string "{",
            TkRightBrace <$ MPC.string "}",
            TkColon <$ MPC.string ":",
            TkComma <$ MPC.string ",",
            anySymbol
          ] ::
            [m Token]
        )

anySymbol :: forall m. MonadLexer m => m Token
anySymbol = toToken <$> MP.some (MP.noneOf (":,{}() \t\n\r\v" :: String))
  where
    toToken "forall" = TkForall
    toToken "∀" = TkUniForall
    toToken "exists" = TkExists
    toToken "∃" = TkUniExists
    toToken "->" = TkRightArrow
    toToken "→" = TkUniRightArrow
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
    toToken s = TkSymbol (Text.pack s)

number :: forall m. MonadLexer m => m (Located Token)
number = located $ TkNumber <$> (hexadecimal <|> octal <|> binary <|> floating <|> decimal)
  where
    hexadecimal = (<>) <$> MPC.string' "0x" <*> (Text.pack <$> MP.some hexDigit)
    octal = (<>) <$> MPC.string' "0o" <*> (Text.pack <$> MP.some octalDigit)
    binary = (<>) <$> MPC.string' "0b" <*> (Text.pack <$> MP.some binDigit)
    floating = MP.empty
    decimal = Text.pack <$> MP.some digit

    hexDigit = MP.oneOf ("0123456789ABCDEFabcdef" :: String)
    octalDigit = MP.oneOf ("01234567" :: String)
    binDigit = MP.oneOf ("01" :: String)
    digit = MP.oneOf ("0123456789" :: String)
