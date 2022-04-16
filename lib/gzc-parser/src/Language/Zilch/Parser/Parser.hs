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

parseNumber :: forall m. MonadParser m => m (Located Text)
parseNumber = do
  let isNumber (TkNumber _) = True
      isNumber _ = False

  TkNumber nb :@ p <- MP.satisfy (isNumber . unLoc)

  pure $ nb :@ p

lexeme :: forall m a. MonadParser m => m a -> m a
lexeme = MPL.lexeme whitespace

whitespace :: forall m. MonadParser m => m ()
whitespace = MPL.space MP.empty skipInlineComment skipMultilineComment
  where
    skipInlineComment = MP.skipSome do
      let isInlineComment (TkInlineComment _) = True
          isInlineComment _ = False
      () <$ MP.satisfy (isInlineComment . unLoc)

    skipMultilineComment = MP.skipSome do
      let isMultilineComment (TkMultilineComment _) = True
          isMultilineComment _ = False
      () <$ MP.satisfy (isMultilineComment . unLoc)

-- | See @'MPL.nonIndented'@.
nonIndented :: forall m a. MonadParser m => m a -> m a
nonIndented = MPL.nonIndented whitespace
{-# INLINE nonIndented #-}

-- | See @'MPL.indentBlock'@.
indentBlock :: forall m a. MonadParser m => m a -> m [a]
indentBlock p = do
  pos <- whitespace *> MPL.indentLevel
  p `MP.sepBy1` indentGuard EQ pos

-- | See @'MPL.lineFold'@.
lineFold :: forall m a. MonadParser m => (m () -> m a) -> m a
lineFold = MPL.lineFold whitespace
{-# INLINE lineFold #-}

-- | See @'MPL.indentGuard'@.
indentGuard :: forall m. MonadParser m => Ordering -> MP.Pos -> m MP.Pos
indentGuard = MPL.indentGuard whitespace
{-# INLINE indentGuard #-}

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
    Mod
      <$> pure []
      <*> MP.many (lexeme parseTopLevelDefinition)
      <* token TkEOF
  where
    removeFrontComments = lexeme (pure ())

parseTopLevelDefinition :: forall m. MonadParser m => m (Located TopLevelDefinition)
parseTopLevelDefinition = located do
  TopLevel
    <$> pure []
    <*> (isJust <$> MP.optional (lexeme $ token TkPublic))
    <*> MP.choice
      ([nonIndented $ lineFold parseLet] :: [m (Located Definition)])

parseLet :: forall m. MonadParser m => m () -> m (Located Definition)
parseLet s = lexeme $ located do
  tk <- lexeme (token TkLet <|> token TkRec)
  (if unLoc tk == TkLet then Let else Rec)
    <$> lexeme parseIdentifier
    <*> MP.many (lexeme $ parseParameter s)
    <*> MP.optional (lexeme (token TkColon) *> lexeme (parseExpression s))
    <*> (lexeme (token TkColonEquals <|> token TkUniColonEquals) *> parseExpression s)

parseParameter :: forall m. MonadParser m => m () -> m (Located Parameter)
parseParameter s =
  located $
    MP.choice
      ( [ lexeme (token TkLeftParen) *> lexeme explicit <* token TkRightParen,
          lexeme (token TkLeftBrace) *> lexeme implicit <* token TkRightBrace,
          Explicit <$> parseIdentifier <*> pure Nothing
        ] ::
          [m Parameter]
      )
  where
    explicit = Explicit <$> lexeme parseIdentifier <*> MP.optional (lexeme (token TkColon) *> parseExpression s)
    implicit = Implicit <$> lexeme parseIdentifier <*> MP.optional (lexeme (token TkColon) *> parseExpression s)

parseExpression :: forall m. MonadParser m => m () -> m (Located Expression)
parseExpression s = located do
  MP.choice
    ( [ EId <$> parseIdentifier,
        EInt . unLoc
          <$> parseNumber,
        parseLambda s,
        parseDo s,
        ELet <$> lexeme (parseLet s) <*> parseExpression s,
        parseForall s,
        parseExists s
      ] ::
        [m Expression]
    )

parseLambda :: forall m. MonadParser m => m () -> m Expression
parseLambda s = do
  _ <- lexeme (token TkLam <|> token TkUniLam)
  param <- lexeme $ parseParameter s
  -- TODO: check if explicit parameter
  _ <- lexeme (token TkRightArrow <|> token TkUniRightArrow)
  expr <- lineFold parseExpression
  pure $ ELam param expr

parseDo :: forall m. MonadParser m => m () -> m Expression
parseDo s = do
  _ <- lexeme (token TkDo)
  expr <- lineFold parseExpression
  pure $ EDo expr

parseForall :: forall m. MonadParser m => m () -> m Expression
parseForall s = do
  _ <- lexeme (token TkForall <|> token TkUniForall)
  params <- lexeme $ MP.many (parseParameter s)
  _ <- lexeme (token TkComma)
  expr <- parseExpression s
  pure $ EForall params expr

parseExists :: forall m. MonadParser m => m () -> m Expression
parseExists s = do
  _ <- lexeme (token TkExists <|> token TkUniExists)
  params <- lexeme $ MP.many (parseParameter s)
  _ <- lexeme (token TkComma)
  expr <- parseExpression s
  pure $ EExists params expr
