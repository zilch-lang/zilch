{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-@ LIQUID "--max-case-expand=0" @-}

module Syntax.Parser (runParser) where

import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.Foldable (foldl')
import Data.Functor ((<&>))
import Data.List (intercalate)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, Position (..), addReport, def)
import Error.Diagnose.Compat.Megaparsec (errorDiagnosticFromBundle)
import Located (Located (..), getPos, unLoc)
import qualified Syntax.CST as CST
import Syntax.Errors
import Syntax.Tokens (Token (..), showToken)
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char.Lexer as MPL

type MonadParser m = (MonadWriter [ParsingWarning] m, MP.MonadParsec ParsingError [Located Token] m, MonadFail m)

instance MP.VisualStream [Located Token] where
  showTokens _ = commaSeparated . fmap (showToken . unLoc) . NonEmpty.toList
    where
      commaSeparated :: [String] -> String
      commaSeparated l = intercalate ", " $ filter (/= "") l

instance MP.TraversableStream [Located Token] where
  reachOffsetNoLine o MP.PosState {..} =
    let (_, after) = splitAt (o - pstateOffset) pstateInput

        actualisePos pos Nothing = pos
        actualisePos _ (Just (Position (bLine, bCol) _ file)) =
          MP.SourcePos
            { MP.sourceName = file,
              MP.sourceColumn = MP.mkPos bCol,
              MP.sourceLine = MP.mkPos bLine
            }

        tokenPos = case after of
          [] -> Nothing
          (_ :@ p) : _ -> Just p

        newPos =
          MP.PosState
            { MP.pstateInput = after,
              MP.pstateOffset = max pstateOffset o,
              MP.pstateSourcePos = actualisePos pstateSourcePos tokenPos,
              MP.pstateTabWidth = pstateTabWidth,
              MP.pstateLinePrefix = pstateLinePrefix
            }
     in newPos

------------------------------------------------------------------------

{-@ ignore located @-}
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
          (MP.unPos beginLine, MP.unPos beginColumn)
          (endLine, endColumn)
          file

  pure $ res :@ pos

{-@ ignore token @-}
-- | Accepts the given 'Token' not matter its position.
token :: forall m. MonadParser m => Token -> m (Located Token)
token tk = MP.satisfy ((== tk) . unLoc) MP.<?> showToken tk

{-@ ignore whitespaces @-}
whitespaces :: forall m. MonadParser m => m ()
whitespaces = MPL.space MP.empty parseLineComment parseMultiComment
  where
    parseLineComment = MP.skipSome $ MP.satisfy lineComment
    lineComment (TkInlineComment _ :@ _) = True
    lineComment _ = False

    parseMultiComment = MP.skipSome $ MP.satisfy multiComment
    multiComment (TkMultilineComment _ :@ _) = True
    multiComment (TkDocComment _ :@ _) = True
    multiComment _ = False

{-@ ignore lexeme @-}
lexeme :: forall m a. MonadParser m => m a -> m a
lexeme = MPL.lexeme whitespaces

{-@ ignore indentGuard @-}
-- | See 'MPL.indentGuard'.
indentGuard :: forall m. MonadParser m => Ordering -> MP.Pos -> m MP.Pos
indentGuard = MPL.indentGuard whitespaces

{-@ ignore nonIndented @-}
nonIndented :: forall m a. MonadParser m => m a -> m a
nonIndented = MPL.nonIndented whitespaces

{-@ ignore lineFold @-}
lineFold :: forall m a. MonadParser m => (m () -> m a) -> m a
lineFold p = MPL.lineFold whitespaces (p . MP.try)

{-@ ignore indentBlock @-}
-- | Unfortunately, we cannot use 'MPL.indentBlock' because it has a constraint @'Token' s ~ 'Char'@,
--   which is not our case here.
indentBlock :: forall m a. MonadParser m => m a -> m [a]
indentBlock p = do
  pos <- whitespaces *> MPL.indentLevel
  (p <* whitespaces) `MP.sepBy` indentGuard EQ pos

{-@ ignore parens @-}
parens :: forall m a. MonadParser m => m a -> m a
parens p = do
  _ <- lexeme (token TkLeftParen)
  res <- p
  _ <- lexeme (token TkRightParen)
  pure res

------------------------------------------------------------------------

{-@ ignore parseIdentifier @-}
parseIdentifier :: forall m. MonadParser m => m (Located String)
parseIdentifier = MP.label "an identifier" $ MP.satisfy isIdentifier <&> \(TkSymbol id :@ p) -> Text.unpack id :@ p
  where
    isIdentifier (TkSymbol _ :@ _) = True
    isIdentifier _ = False

{-@ ignore parseNumber @-}
parseNumber :: forall m. MonadParser m => m (Located String, Maybe (Located String))
parseNumber = MP.label "a number" do
  TkNumber nb suffix :@ p <- MP.satisfy isNumber
  pure (Text.unpack nb :@ p, (:@ p) . Text.unpack <$> suffix)
  where
    isNumber (TkNumber _ _ :@ _) = True
    isNumber _ = False

------------------------------------------------------------------------

{-@ ignore runParser @-}
runParser :: FilePath -> [Located Token] -> Either (Diagnostic String) (Located CST.Module, Diagnostic String)
runParser path tokens =
  bimap
    (errorDiagnosticFromBundle Nothing "Parse error on input" Nothing)
    (second toDiagnostic)
    $ MP.runParser (runWriterT parseModule) path tokens
  where
    toDiagnostic = foldl' addReport def . fmap fromParsingWarning

------------------------------------------------------------------------

{-@ ignore parseModule @-}
parseModule :: forall m. MonadParser m => m (Located CST.Module)
parseModule = located do
  defs <- MP.many (nonIndented parseTopLevel)
  _ <- token TkEOF MP.<?> "end of input"
  pure $ CST.Mod defs

{-@ ignore parseTopLevel @-}
parseTopLevel :: forall m. MonadParser m => m (Located CST.TopLevel)
parseTopLevel = located $ lineFold \s -> do
  isPub <- MP.option False (True <$ lexeme (token TkPublic))
  def <- parseDefinition s
  pure $ CST.Binding isPub def

{-@ ignore parseDefinition @-}
parseDefinition :: forall m. MonadParser m => m () -> m (Located CST.Definition)
parseDefinition s =
  located $
    MP.choice
      [parseLet s, parseRec s, parseVal s, parseAssume s, parseMutual s]
  where
    parseLet = parseLetOrRec TkLet CST.Let
    parseRec = parseLetOrRec TkRec CST.Rec

    parseLetOrRec tk ctor s = do
      _ <- lexeme (token tk) <* s
      mult <- MP.optional (parseMultiplicity s <* s)
      name <- parseIdentifier <* s
      params <- lexeme (parseLambdaParameter s) `MP.sepBy` s
      ret <- MP.optional do
        _ <- lexeme (token TkColon) <* s
        parseFullExpression s
      _ <- lexeme (token TkColonEquals MP.<|> token TkUniColonEquals) <* s
      body <- parseFullExpression s

      pure $ ctor mult name params ret body

    parseVal s = do
      _ <- lexeme (token TkVal) <* s
      mult <- MP.optional (parseMultiplicity s <* s)
      name <- parseIdentifier <* s
      params <- lexeme (parseTypeParameter s) `MP.sepBy` s
      _ <- lexeme (token TkColon) <* s
      ret <- parseFullExpression s

      pure $ CST.Val mult name params ret

    parseAssume s = do
      _ <- lexeme (token TkAssume) <* s
      params <- lexeme (parseTypeParameter s) `MP.sepBy` s

      pure $ CST.Assume params

    parseMutual s = do
      _ <- lexeme (token TkMutual)
      defs <- indentBlock (s *> parseDefinition s)

      pure $ CST.Mutual defs

{-@ ignore parseMultiplicity @-}
parseMultiplicity :: forall m. MonadParser m => m () -> m (Located CST.Multiplicity)
parseMultiplicity s = do
  _ :@ Position _ (_, cl) _ <- token TkAt
  MP.observing (indentGuard EQ (MP.mkPos cl)) >>= \case
    Left _ -> fail "Unexpected blank after '@'"
    Right _ -> pure ()
  parseAtomicExpression s

{-@ ignore parseAtomicExpression @-}
parseAtomicExpression :: forall m. MonadParser m => m () -> m (Located CST.Expression)
parseAtomicExpression s =
  located $
    MP.choice
      [ -- identifiers
        CST.Identifier . unLoc <$> parseIdentifier,
        -- numbers
        do
          (nb, suffix) <- parseNumber
          -- FIXME: do that only if @nb@ does not contain dots
          pure $ CST.Integer nb (fmap CST.Identifier <$> suffix),
        -- multiplicative unit
        MP.try
          do
            _ <- lexeme (token TkLeftParen)
            _ <- lexeme (token TkRightParen)
            pure CST.MultiplicativeUnit,
        -- multiplicative unit type
        CST.MultiplicativeUnitType <$ token (TkSymbol "𝟏"),
        -- parenthesized expression
        CST.Parenthesized
          <$> parens (parseFullExpression s)
      ]

{-@ ignore parseFullExpression @-}
parseFullExpression :: forall m. MonadParser m => m () -> m (Located CST.Expression)
parseFullExpression s =
  MP.label "an expression" . located $
    MP.choice
      [ -- lambda abstraction
        parseLambda s,
        -- do block
        parseDo s,
        -- local binding
        parseLocal s,
        -- dependent type
        MP.try $ parseDependentType s,
        -- function application
        parseApplication s
      ]

{-@ ignore parseLambda @-}
parseLambda :: forall m. MonadParser m => m () -> m CST.Expression
parseLambda _ = lineFold \s -> do
  _ <- lexeme (token TkLam MP.<|> token TkUniLam) <* s
  params <- parseLambdaParameter s `MP.sepBy1` s
  _ <- lexeme (token TkDoubleRightArrow MP.<|> token TkUniDoubleRightArrow) <* s
  body <- parseFullExpression s

  pure $ CST.Lambda params body

{-@ ignore parseDo @-}
parseDo :: forall m. MonadParser m => m () -> m CST.Expression
parseDo _ = lineFold \s -> do
  _ <- lexeme (token TkDo) <* s
  body <- parseFullExpression s

  pure $ CST.Do body

{-@ ignore parseLocal @-}
parseLocal :: forall m. MonadParser m => m () -> m CST.Expression
parseLocal s = do
  def <- lineFold parseDefinition <* s
  body <- parseFullExpression s

  pure $ CST.Local def body

{-@ ignore parseDependentType @-}
parseDependentType :: forall m. MonadParser m => m () -> m CST.Expression
parseDependentType s = do
  params <- parseTypeParameter s <* s
  tk :@ _ <-
    lexeme $
      MP.choice
        [ token TkAmpersand,
          token TkTimes,
          token TkUniTensor,
          token TkRightArrow,
          token TkUniRightArrow
        ]
        <* s
  ret <- parseFullExpression s

  let ctor = case tk of
        TkAmpersand -> CST.AdditiveSigmaType
        TkUniTensor -> CST.MultiplicativeSigmaType
        TkTimes -> CST.MultiplicativeSigmaType
        TkRightArrow -> CST.ProductType
        TkUniRightArrow -> CST.ProductType

  pure $ ctor params ret

{-@ ignore parseApplication @-}
parseApplication :: forall m. MonadParser m => m () -> m CST.Expression
parseApplication s = do
  fn <- lexeme (parseAtomicExpression s)
  args <-
    MP.many $
      MP.choice
        [ s *> go TkLeftParen TkRightParen CST.Explicit,
          s *> go TkLeftBrace TkRightBrace CST.Implicit
        ]

  pure
    if null args
      then unLoc fn
      else CST.Application fn args
  where
    go left right imp = do
      _ <- lexeme (token left) <* s
      args <- parseFullExpression s `MP.sepBy` (s *> lexeme (token TkComma) <* s)
      _ <- s *> token right

      pure (imp, args)

{-@ ignore parseTypeParameter @-}
parseTypeParameter :: forall m. MonadParser m => m () -> m [Located CST.Parameter]
parseTypeParameter s =
  MP.choice
    [ go TkLeftParen TkRightParen CST.Explicit s,
      go TkLeftBrace TkRightBrace CST.Implicit s,
      pure <$> located do
        mult <- MP.optional $ lexeme (parseMultiplicity s) <* s
        typ <- parseAtomicExpression s
        pure $ CST.Parameter CST.Explicit mult Nothing (Just typ)
    ]
  where
    go left right imp s = do
      _ <- lexeme (token left) <* s
      params <- parseParam imp s `MP.sepBy` (s *> lexeme (token TkComma) <* s)
      _ <- token right

      pure params

    parseParam imp s = located do
      mult <- MP.optional $ lexeme (parseMultiplicity s) <* s
      (name, typ) <-
        MP.choice
          [ MP.try do
              name <- lexeme (unnamedBinding MP.<|> parseIdentifier) <* s
              _ <- lexeme (token TkColon) <* s
              typ <- parseFullExpression s <* s
              pure (Just name, Just typ),
            do
              typ <- parseFullExpression s
              pure (Nothing, Just typ)
          ]

      pure $ CST.Parameter imp mult name typ

    unnamedBinding = ("_" <$) <$> token TkUnderscore

{-@ ignore parseLambdaParameter @-}
parseLambdaParameter :: forall m. MonadParser m => m () -> m [Located CST.Parameter]
parseLambdaParameter s =
  MP.choice
    [ pure <$> located do
        name <- parseIdentifier
        pure $ CST.Parameter CST.Explicit Nothing (Just name) Nothing,
      go TkLeftParen TkRightParen CST.Explicit s,
      go TkLeftBrace TkRightBrace CST.Implicit s
    ]
  where
    go left right imp s = do
      _ <- lexeme (token left) <* s
      params <- parseParam imp s `MP.sepBy` (s *> lexeme (token TkComma) <* s)
      _ <- lexeme (token right) <* s

      pure params

    parseParam imp s = located do
      mult <- MP.optional $ lexeme (parseMultiplicity s) <* s
      name <- parseIdentifier <* s
      typ <- MP.optional do
        _ <- lexeme (token TkColon) <* s
        parseFullExpression s

      pure $ CST.Parameter imp mult (Just name) typ
