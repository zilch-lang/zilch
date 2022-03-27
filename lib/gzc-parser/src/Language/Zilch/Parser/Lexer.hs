{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Zilch.Parser.Lexer where

import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.Foldable (foldl')
import Data.Located (Located)
import Data.Text (Text)
import Error.Diagnose (Diagnostic, addReport, def)
import Error.Diagnose.Compat.Megaparsec
import Language.Zilch.Parser.Core (Token (..))
import Language.Zilch.Parser.Errors (LexicalError, LexicalWarning, fromLexicalWarning)
import Language.Zilch.Parser.Internal (located)
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
token = MP.choice ([comment] :: [m (Located Token)])

eof :: MonadLexer m => m (Located Token)
eof = located (TkEOF <$ MP.eof)

comment :: MonadLexer m => m (Located Token)
comment = undefined
