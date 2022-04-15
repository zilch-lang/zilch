{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Zilch.Parser.Parser where

import Control.Applicative ((<|>))
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.List (foldl')
import Data.Located (Located ((:@)), unLoc)
import Data.Maybe (isJust)
import Data.Text (Text)
import Error.Diagnose (Diagnostic, addReport, def)
import Error.Diagnose.Compat.Megaparsec (errorDiagnosticFromBundle)
import Language.Zilch.Parser.Core
import Language.Zilch.Parser.Errors
import Language.Zilch.Parser.Internal (located)
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char.Lexer as MPL

type MonadParser m = (MonadWriter [ParsingWarning] m, MP.MonadParsec ParsingError [Located Token] m, MonadFail m)

token :: forall m. MonadParser m => Token -> m (Located Token)
token tk = MP.satisfy ((== tk) . unLoc)

parseIdentifier :: forall m. MonadParser m => m (Located Text)
parseIdentifier = do
  let isIdent (TkSymbol _) = True
      isIdent _ = False

  TkSymbol ident :@ p <- MP.satisfy (isIdent . unLoc)

  pure $ ident :@ p

lexeme :: forall m a. MonadParser m => m a -> m a
lexeme = MPL.lexeme (MPL.space (pure ()) skipInlineComment skipMultilineComment)
  where
    skipInlineComment = do
      let isInlineComment (TkInlineComment _) = True
          isInlineComment _ = False
      () <$ MP.satisfy (isInlineComment . unLoc)

    skipMultilineComment = do
      let isMultilineComment (TkMultilineComment _) = True
          isMultilineComment _ = False
      () <$ MP.satisfy (isMultilineComment . unLoc)

--------------------------------------------------

parseTokens :: FilePath -> [Located Token] -> Either (Diagnostic String) (Located Module, Diagnostic String)
parseTokens filename content =
  bimap
    (errorDiagnosticFromBundle "Parse error on input" Nothing)
    (second toDiagnostic)
    $ MP.runParser (runWriterT parseModule) filename content
  where
    toDiagnostic warns = foldl' addReport def (fromParsingWarning <$> warns)

parseModule :: forall m. MonadParser m => m (Located Module)
parseModule =
  located do
    removeFrontComments
    Mod <$> pure []
      <*> MP.many (lexeme parseTopLevelDefinition)
  where
    removeFrontComments = lexeme (pure ())

parseTopLevelDefinition :: forall m. MonadParser m => m (Located TopLevelDefinition)
parseTopLevelDefinition = located do
  TopLevel <$> pure []
    <*> (isJust <$> MP.optional (lexeme $ token TkPublic))
    <*> MP.choice
      ([parseLet] :: [m (Located Definition)])

parseLet :: forall m. MonadParser m => m (Located Definition)
parseLet = lexeme $ located do
  Let <$> lexeme parseIdentifier
    <*> MP.many (lexeme parseParameter)
    <*> MP.optional (lexeme (token TkColon) *> lexeme parseExpression)
    <*> (lexeme (token TkColonEquals <|> token TkUniColonEquals) *> parseExpression)

parseParameter :: forall m. MonadParser m => m (Located Parameter)
parseParameter = MP.empty -- TODO

parseExpression :: forall m. MonadParser m => m (Located Expression)
parseExpression = MP.empty -- TODO
