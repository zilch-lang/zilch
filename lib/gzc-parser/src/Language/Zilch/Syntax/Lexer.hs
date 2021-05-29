{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Zilch.Syntax.Lexer (runLexer) where

import qualified Text.Megaparsec as MP
import Control.Monad.State (evalState, MonadState, put, gets)
import Data.Text (Text)
import Language.Zilch.Core.Tokens (LToken, Token(..))
import Text.Diagnose (Diagnostic, Position(..))
import Data.Bifunctor (Bifunctor(first))
import qualified Text.Megaparsec.Char.Lexer as MPL
import qualified Text.Megaparsec.Char as MPC
import Data.Maybe (catMaybes)
import Data.IndentLocated (Located, IndentLocated (ILocated))
import Control.Applicative (liftA2, (<|>), empty)
import qualified Data.Text as Text
import Data.Char (isPrint, isDigit, isSpace)
import Language.Zilch.Syntax.Internal (megaparsecBundleToDiagnostic)
import Language.Zilch.Syntax.Errors (LexerError(..))

type Lexer m = (MP.MonadParsec LexerError Text m, MonadState Int m)

-- | Runs the lexer on a given input file.
runLexer :: Text                                         -- ^ The content of the file
         -> String                                       -- ^ The name of the file
         -> Either (Diagnostic [] String Char) [LToken]  -- ^ Either an error or a list of tokens
runLexer content filename = evalState (first toDiagnostic <$> MP.runParserT tokenizeModule filename content) 0

-- | Transforms a 'ParseErrorBundle' into a 'Diagnostic'.
toDiagnostic :: MP.ParseErrorBundle Text LexerError -> Diagnostic [] String Char
toDiagnostic = megaparsecBundleToDiagnostic "Lexing error on input"
{-# INLINE toDiagnostic #-}

-------------------------------------------------------------------------------------

tokenizeModule :: Lexer m => m [LToken]
tokenizeModule = catMaybes <$> MP.many (lexeme token) <* MP.eof
{-# INLINE tokenizeModule #-}

-- | Consumes any non-newline whitespace characters after running a parser.
lexeme :: Lexer m => m a -> m a
lexeme p = MPL.lexeme (MPL.space MPC.hspace1 empty empty) p       -- NOTE: do not eta-reduce
{-# INLINE lexeme #-}

-- | Transforms a simple parser into a parser returning a located value.
located :: Lexer m => m a -> m (Located a)
located p = do
  currentIndent <- gets fromIntegral

  MP.SourcePos file beginLine beginColumn <- MP.getSourcePos
  res <- p
  MP.SourcePos _ endLine endColumn <- MP.getSourcePos

  let pos = Position (fromIntegral $ MP.unPos beginLine, fromIntegral $ MP.unPos beginColumn)
                     (fromIntegral $ MP.unPos endLine, fromIntegral $ MP.unPos endColumn)
                     file

  pure (ILocated pos currentIndent res)

------------------------------------------------------------------------------------

-- | Tries to parse a token.
--
--   Returns 'Nothing' if nothing is to be returned (for example in the case of an end-of-line).
token :: Lexer m => m (Maybe LToken)
token = MP.choice
  [ Nothing <$  eol
  , Just    <$> MP.try inlineComment
  , Just    <$> specialSymbol
  , Just    <$> numberLiteral
  , Just    <$> stringLiteral
  , Just    <$> characterLiteral
  , Just    <$> anySymbol
  ]
  where
    eol = MP.some $ MPC.eol *> do
      o1 <- MP.getOffset
      o2 <- lexeme MP.getOffset    -- NOTE: a space counts as a parsed token; because `getSourcePos` is not cheap,
      put (o2 - o1)                --       `getOffset` works just as well to get the indentation level of the current line

-- | Parses an inline comment, beginning with @--@ and a space character.
inlineComment :: Lexer m => m LToken
inlineComment = lexeme . located $ InlineComment . Text.pack <$> (MPC.string "--" *> MPC.hspace *> MP.manyTill (f (&&) (/=)) (f (||) (==)))
  where f comb op = MP.satisfy (liftA2 comb (`op` '\n') (`op` '\r'))
        {-# INLINE f #-}

-- | A special symbol cannot appear in identifiers.
--
---  All the special symbols in Zilch are also special tokens: @(@, @)@, @{@, @}@, @[@, @]@ and @,@
specialSymbol :: Lexer m => m LToken
specialSymbol = lexeme . located $ MP.choice
  [ LParen <$ MPC.char '(', RParen <$ MPC.char ')'
  , LBrack <$ MPC.char '[', RBrack <$ MPC.char ']'
  , LBrace <$ MPC.char '[', RBrace <$ MPC.char ']'
  , Comma  <$ MPC.char ','
  ]

-- | Parses a number literal according to the specification.
numberLiteral :: Lexer m => m LToken
numberLiteral = lexeme . located $ MP.choice
  [ integer "0b" binaryDigit
  , integer "0o" octalDigit
  , integer "0x" hexadecimalDigit
  , Integer . Text.pack <$> MP.some decimalDigit
  ]
  where
    integer prefix digit = Integer <$> ((<>) <$> MPC.string' prefix <*> (Text.pack <$> MP.some digit))
    {-# INLINE integer #-}

    binaryDigit, octalDigit, decimalDigit, hexadecimalDigit :: Lexer m => m Char
    binaryDigit      = MP.satisfy (liftA2 (||) (== '0') (== '1'))
    octalDigit       = MP.oneOf ("01234567" :: String)
    decimalDigit     = MP.oneOf ("0123456789" :: String)
    hexadecimalDigit = MP.oneOf ("0123456789abcdefABCDEF" :: String)
    {-# INLINE binaryDigit #-}
    {-# INLINE octalDigit #-}
    {-# INLINE decimalDigit #-}
    {-# INLINE hexadecimalDigit #-}

-- | Parses a string literal with escape characters.
stringLiteral :: Lexer m => m LToken
stringLiteral = lexeme . located $ String . mconcat <$> do
  sep1 <- Text.singleton <$> MPC.char '"'
  content <- mconcat <$> MP.many (escapeCharacter <|> anyCharacter)
  sep2 <- Text.singleton <$> MPC.char '"'
  pure [sep1, content, sep2]
  where
    anyCharacter = Text.singleton <$> MP.satisfy \ c -> (c /= '\n') && (c /= '\r') && (c /= '\'')
    {-# INLINE anyCharacter #-}

-- | Parses a character literal with escape characters.
characterLiteral :: Lexer m => m LToken
characterLiteral = lexeme . located $ Character . mconcat <$> do
  sep1 <- Text.singleton <$> MPC.char '\''
  char <- escapeCharacter <|> anyCharacter
  sep2 <- Text.singleton <$> MPC.char '\''
  pure [sep1, char, sep2]
  where
    anyCharacter = Text.singleton <$> MP.satisfy \ c -> (c /= '\n') && (c /= '\r') && (c /= '\'')
    {-# INLINE anyCharacter #-}

-- | Parses any escape sequence among @\a@, @\b@, @\f@, @\n@, @\r@, @\t@, @\v@, @\\@, @\"@ and @\'@.
escapeCharacter :: Lexer m => m Text
escapeCharacter = (<>) <$> (Text.singleton <$> MPC.char '\\')
                       <*> (Text.singleton <$> MP.choice [ MPC.char 'a', MPC.char 'b', MPC.char 'f', MPC.char 'n', MPC.char 'r'
                                                         , MPC.char 't', MPC.char 'v', MPC.char '\\', MPC.char '"', MPC.char '\''
                                                         , MP.anySingle >>= MP.customFailure . InvalidEscapeSequence
                                                         ])

-- | Parses any symbol, ranging from keywords to basic identifiers.
anySymbol :: Lexer m => m LToken
anySymbol = lexeme $ located do
  h <- MP.satisfy \ c -> isPrint c && not (isDigit c) && not (isSpecial c)
  r <- MP.many (MP.satisfy (not . isSpace))
  pure $ matchesKeyword (h : r)
  where
    matchesKeyword "forall"     = Forall
    matchesKeyword "∀"          = UniForall
    matchesKeyword "def"        = Def
    matchesKeyword "enum"       = Enum
    matchesKeyword "record"     = Record
    matchesKeyword "class"      = Class
    matchesKeyword "impl"       = Impl
    matchesKeyword "where"      = Where
    matchesKeyword "do"         = Do
    matchesKeyword "type"       = Type
    matchesKeyword "case"       = Case
    matchesKeyword "of"         = Of
    matchesKeyword "module"     = Module
    matchesKeyword "fn"         = Fn
    matchesKeyword "foreign"    = Foreign
    matchesKeyword "as"         = As
    matchesKeyword "open"       = Open
    matchesKeyword "import"     = Import
    matchesKeyword "export"     = Export
    matchesKeyword "perm"       = Perm
    matchesKeyword "if"         = If
    matchesKeyword "then"       = Then
    matchesKeyword "else"       = Else
    matchesKeyword "pattern"    = Pattern
    matchesKeyword ":="         = ColonEquals
    matchesKeyword "≔"          = UniColonEquals
    matchesKeyword "<-"         = LeftArrow
    matchesKeyword "←"          = UniLeftArrow
    matchesKeyword "<:"         = LessColon
    matchesKeyword "->"         = RightArrow
    matchesKeyword "→"          = UniRightArrow
    matchesKeyword "_"          = Underscore
    matchesKeyword "·"          = UniUnderscore
    matchesKeyword "?"          = Question
    matchesKeyword ":"          = Colon
    matchesKeyword "#"          = Hash
    matchesKeyword name         = Identifier (Text.pack name)
    {-# INLINE matchesKeyword #-}

-- | Checks whether the input character is a special character (which can be parsed with 'specialSymbol') that cannot be part of an identifier.
isSpecial :: Char -> Bool
isSpecial '{' = True
isSpecial '}' = True
isSpecial '[' = True
isSpecial ']' = True
isSpecial '(' = True
isSpecial ')' = True
isSpecial ',' = True
isSpecial _   = False
{-# INLINE isSpecial #-}
