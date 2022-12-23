{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

module Syntax.Tokens where

import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text

-- | The entire set of possible tokens in the language.
data Token
  = -- | @let@: variable/function binding in the current scope
    TkLet
  | -- | @rec@: recursive function binding in the current scope
    TkRec
  | -- | @enum@: enumeration declarator
    TkEnum
  | -- | @record@: record declarator
    TkRecord
  | -- | @public@: export from module
    TkPublic
  | -- | @val@: field declarator
    TkVal
  | -- | @import@: module import
    TkImport
  | -- | @as@: binding aliasing in import group
    TkAs
  | -- | @lam@: anonymous function introduction
    TkLam
  | -- | @open@: introduce functions from records/enums
    TkOpen
  | -- | @λ@: @lam@ but Unicode
    TkUniLam
  | -- | @do@: anonymous function without parameter (alias to @lam() =>@)
    TkDo
  | -- | @type@: the builtin type of types
    TkType
  | -- | @assume@: parameter introduction
    TkAssume
  | -- | @if@
    TkIf
  | -- | @then@
    TkThen
  | -- | @else@
    TkElse
  | -- | @mutual@
    TkMutual
  | -- | @#attributes@
    TkHashAttributes
  | -- | @:@: @id : type@ means that the binding @id@ has the type @type@
    TkColon
  | -- | @:=@: binding definition
    TkColonEquals
  | -- | @≔@: @:=@ but Unicode
    TkUniColonEquals
  | -- | @(@: left/opening parenthesis
    TkLeftParen
  | -- | @)@: right/closing parenthesis
    TkRightParen
  | -- | @{{@: double left/opening curly bracket
    TkDoubleLeftBrace
  | -- | @⦃@: @{{@ but unicode
    TkUniDoubleLeftBrace
  | -- | @}}@: double right/closing curly bracket
    TkDoubleRightBrace
  | -- | @⦄@: @}}@ but unicode
    TkUniDoubleRightBrace
  | -- | @{@: left/opening curly bracket
    TkLeftBrace
  | -- | @}@: right/closing curly bracket
    TkRightBrace
  | -- | @⟨@: left/opening angle
    TkLeftAngle
  | -- | @⟩@: right/closing angle
    TkRightAngle
  | -- | @::@: module/record access
    TkDoubleColon
  | -- | @∷@: @::@ but Unicode
    TkUniDoubleColon
  | -- | @->@: function type
    TkRightArrow
  | -- | @→@: @->@ but Unicode
    TkUniRightArrow
  | -- | @=>@: lambda expression separator
    TkDoubleRightArrow
  | -- | @⇒@: @=>@ but Unicode
    TkUniDoubleRightArrow
  | -- | @×@: multiplicative pair separator
    TkTimes
  | -- | @⊗@: @×@ but Unicode
    TkUniTensor
  | -- | @&@: additive pair separator
    TkAmpersand
  | -- | @true@
    TkTrue
  | -- | @false@
    TkFalse
  | -- | @,@: common separator
    TkComma
  | -- | @_@: wildcard pattern or infered holes
    TkUnderscore
  | -- | @\@@: multiplicity syntactic prefix
    TkAt
  | -- | A valid symbol formed from any non-space character
    TkSymbol Text
  | -- | Any number-like form
    TkNumber Text (Maybe Text)
  | -- | Any character-like enclosed in @'@
    TkCharacter Text
  | -- | A sequence of characters enclosed in @"@
    TkString Text
  | -- | The end of the file (EOF)
    TkEOF
  | -- | Inline comment started with @--@ until the next end of line
    TkInlineComment Text
  | -- | Multiline comment, enclosed by @/-@ and @-/@
    TkMultilineComment Text
  | -- | A special kind of multiline comment, enclosed by @/--@ and @-/@
    TkDocComment Text
  deriving (Show, Eq, Ord)

-- | A prettier output for 'Token's than the corresponding derived 'Show' instance.
showToken :: Token -> String
showToken TkLet = "'let'"
showToken TkRec = "'rec'"
showToken TkVal = "'val'"
showToken TkOpen = "'open'"
showToken TkEnum = "'enum'"
showToken TkRecord = "'record'"
showToken TkPublic = "'public'"
showToken TkImport = "'import'"
showToken TkAs = "'as'"
showToken TkLam = "'lam'"
showToken TkUniLam = "'λ'"
showToken TkDo = "'do'"
showToken TkColon = "':'"
showToken TkColonEquals = "':='"
showToken TkUniColonEquals = "'≔'"
showToken TkLeftParen = "'('"
showToken TkRightParen = "')'"
showToken TkDoubleLeftBrace = "'{{'"
showToken TkUniDoubleLeftBrace = "'⦃'"
showToken TkDoubleRightBrace = "'}}'"
showToken TkUniDoubleRightBrace = "'⦄'"
showToken TkLeftBrace = "'{'"
showToken TkRightBrace = "'}'"
showToken TkDoubleColon = "'::'"
showToken TkUniDoubleColon = "'∷'"
showToken TkRightArrow = "'->'"
showToken TkUniRightArrow = "'→'"
showToken TkDoubleRightArrow = "'=>'"
showToken TkUniDoubleRightArrow = "'⇒'"
showToken TkComma = "','"
showToken TkUnderscore = "'_'"
showToken (TkSymbol txt) = "'" <> Text.unpack txt <> "'"
showToken (TkNumber txt suffix) = "'" <> Text.unpack txt <> Text.unpack (fromMaybe "" suffix) <> "'"
showToken (TkCharacter txt) = "''" <> Text.unpack txt <> "''"
showToken (TkString txt) = "'\"" <> Text.unpack txt <> "\"'"
showToken TkEOF = "<eof>"
showToken (TkInlineComment c) = "--" <> Text.unpack c
showToken (TkMultilineComment c) = "/-" <> Text.unpack c <> "-/"
showToken (TkDocComment c) = "/--" <> Text.unpack c <> "-/"
showToken TkType = "'type'"
showToken TkAssume = "'assume'"
showToken TkTrue = "'true'"
showToken TkFalse = "'false'"
showToken TkIf = "'if'"
showToken TkThen = "'then'"
showToken TkElse = "'else'"
showToken TkMutual = "'mutual'"
showToken TkUniTensor = "'⊗'"
showToken TkTimes = "'×'"
showToken TkAmpersand = "'&'"
showToken TkLeftAngle = "'⟨'"
showToken TkRightAngle = "'⟩'"
showToken TkHashAttributes = "'#attributes'"
showToken TkAt = "'@'"
