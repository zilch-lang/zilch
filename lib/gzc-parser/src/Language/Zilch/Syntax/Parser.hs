{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Language.Zilch.Syntax.Parser (parseTokens) where

import Control.Applicative ((<|>))
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.List (foldl')
import Data.Located (Located ((:@)), Position (..), getPos, unLoc)
import Data.Maybe (isJust)
import Data.Text (Text)
import Error.Diagnose (Diagnostic, addReport, def)
import Error.Diagnose.Compat.Megaparsec (errorDiagnosticFromBundle)
import Language.Zilch.Syntax.Core
import Language.Zilch.Syntax.Errors
import Language.Zilch.Syntax.Internal ()
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char.Lexer as MPL

type MonadParser m = (MonadWriter [ParsingWarning] m, MP.MonadParsec ParsingError [Located Token] m, MonadFail m)

-- | Transforms a simple parser into a parser returning a located value.
located :: forall m a. MonadParser m => m a -> m (Located a)
located p = do
  MP.SourcePos file beginLine beginColumn <- MP.getSourcePos
  MP.State input0 offset0 _ _ <- MP.getParserState
  -- NOTE: we need to fetch the input stream before, because it is not complete
  -- (it does not necessarily contain all tokens at once).

  res <- p

  MP.State _ offset _ _ <- MP.getParserState
  let Position _ (endLine, endColumn) _ = getPos $ input0 !! (offset - 1 - offset0)

  -- NOTE: We need to fetch the last token parsed, which is located right before the
  --       currently available token.
  --       Thankfully, our tokens have their locations, so we can use the ending location
  --       of the previous token to get the ending location of the result of our parser @p@.

  let pos =
        Position
          (fromIntegral $ MP.unPos beginLine, fromIntegral $ MP.unPos beginColumn)
          (endLine, endColumn)
          file

  pure $ res :@ pos

token :: forall m. MonadParser m => Token -> m (Located Token)
token tk = MP.satisfy ((== tk) . unLoc)

parseIdentifier :: forall m. MonadParser m => m (Located Text)
parseIdentifier = do
  let isIdent (TkSymbol _) = True
      isIdent _ = False

  TkSymbol ident :@ p <- MP.satisfy (isIdent . unLoc)

  pure $ ident :@ p

parseNumber :: forall m. MonadParser m => m (Located (Text, Maybe Text))
parseNumber = do
  let isNumber (TkNumber _ _) = True
      isNumber _ = False

  TkNumber nb suf :@ p <- MP.satisfy (isNumber . unLoc)

  pure $ (nb, suf) :@ p

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
  (p <* whitespace) `MP.sepBy1` indentGuard EQ pos

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
    (errorDiagnosticFromBundle Nothing "Parse error on input" Nothing)
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
parseTopLevelDefinition = located $
  nonIndented $ lineFold \s -> do
    TopLevel
      <$> pure []
      <*> (isJust <$> MP.optional (lexeme (token TkPublic) <* s))
      <*> MP.choice
        ([parseLet s, parseAssume s] :: [m (Located Definition)])

parseLet :: forall m. MonadParser m => m () -> m (Located Definition)
parseLet s = lexeme $ located do
  tk <- lexeme (token TkLet <|> token TkRec) <* s
  (if unLoc tk == TkLet then Let else Rec)
    <$> (MP.optional parseResourceUsage <* s)
    <*> (lexeme parseIdentifier <* s)
    <*> (MP.many (lexeme $ parseParameter s) <* s)
    <*> (MP.optional (lexeme (token TkColon) *> s *> lexeme (parseExpression s)) <* s)
    <*> (lexeme (token TkColonEquals <|> token TkUniColonEquals) *> s *> parseExpression s)

parseAssume :: forall m. MonadParser m => m () -> m (Located Definition)
parseAssume s = lexeme $ located do
  lexeme (token TkAssume) <* s
  Assume <$> (lexeme (parseParameter s) `MP.sepBy1` MP.try s)

parseParameter :: forall m. MonadParser m => m () -> m (Located Parameter)
parseParameter s =
  located $
    MP.choice
      ( [ lexeme (token TkLeftParen) *> s *> lexeme explicit <* s <* token TkRightParen,
          lexeme (token TkLeftBrace) *> s *> lexeme implicit <* s <* token TkRightBrace
        ] ::
          [m Parameter]
      )
  where
    explicit =
      Explicit
        <$> (MP.optional (lexeme parseResourceUsage) <* s)
        <*> (lexeme idOrIgnore <* s)
        <*> MP.optional (lexeme (token TkColon) *> s *> parseExpression s)
    implicit =
      Implicit
        <$> (MP.optional (lexeme parseResourceUsage) <* s)
        <*> (lexeme idOrIgnore <* s)
        <*> MP.optional (lexeme (token TkColon) *> s *> parseExpression s)

    idOrIgnore = parseIdentifier <|> fmap ("_" <$) (token TkUnderscore)

parseResourceUsage :: forall m. MonadParser m => m (Located Integer)
parseResourceUsage = do
  TkNumber usage _ :@ p <- MP.satisfy isUsageNumber
  case usage of
    "0" -> pure (0 :@ p)
    "1" -> pure (1 :@ p)
    _ -> undefined
  where
    isUsageNumber (TkNumber "0" Nothing :@ _) = True
    isUsageNumber (TkNumber "1" Nothing :@ _) = True
    isUsageNumber _ = False

parseExpression :: forall m. MonadParser m => m () -> m (Located Expression)
parseExpression s = located do
  MP.choice
    ( [ EApplication <$> (parseAtom s `MP.sepBy1` MP.try s)
      ] ::
        [m Expression]
    )

parseAtom :: forall m. MonadParser m => m () -> m (Located Expression)
parseAtom s = located do
  MP.choice
    ( [ ELet <$> (lineFold (\s' -> lexeme (parseLet s')) <* s) <*> parseExpression s,
        do
          (nb, suf) :@ _ <- parseNumber
          pure $ EInt nb suf,
        ETypedHole <$ token TkQuestionMark,
        EHole <$ token TkUnderscore,
        parseLambda s,
        parseDo s,
        EType <$ token TkType,
        MP.try $ parsePi s,
        EId <$> parseIdentifier,
        EImplicit <$> (lexeme (token TkLeftBrace) *> lexeme (parseExpression s) <* token TkRightBrace),
        EParens <$> (lexeme (token TkLeftParen) *> lexeme (parseExpression s) <* token TkRightParen)
      ] ::
        [m Expression]
    )

parseLambda :: forall m. MonadParser m => m () -> m Expression
parseLambda s = do
  _ <- lexeme (token TkLam <|> token TkUniLam) <* s
  params <-
    MP.choice
      ( [ MP.try $
            []
              <$ (lexeme (token TkLeftParen) *> token TkRightParen),
          MP.some $ lexeme $ parseParameter s <* s
        ] ::
          [m [Located Parameter]]
      )
  _ <- lexeme (token TkDoubleRightArrow <|> token TkUniDoubleRightArrow) <* s
  expr <- parseExpression s
  pure $ ELam params expr

parseDo :: forall m. MonadParser m => m () -> m Expression
parseDo s = do
  _ <- lexeme (token TkDo) <* s
  expr <- parseExpression s
  pure $ EDo expr

parsePi :: forall m. MonadParser m => m () -> m Expression
parsePi s = do
  param <- lexeme (parseParameter s) <* s
  _ <- lexeme (token TkRightArrow <|> token TkUniRightArrow) <* s
  ret <- parseExpression s
  pure $ EPi param ret
