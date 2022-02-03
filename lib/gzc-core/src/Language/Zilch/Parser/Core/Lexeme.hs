module Language.Zilch.Parser.Core.Lexeme (Token (..)) where

import Data.Text (Text)

-- | The entire set of possible tokens in the language.
data Token
  = -- | @let@: variable/function binding in the current scope
    TkLet
  | -- | @rec@: recursive function binding in the current scope
    TkRec
  | -- | @exporŧ@: module export group
    TkExport
  | -- | @import@: module import
    TkImport
  | -- | @as@: binding aliasing in import group
    TkAs
  | -- | @lam@: anonymous function introduction
    TkLam
  | -- | @λ@: @lam@ but Unicode
    TkUniLam
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
  | -- | @::@: module/record access
    TkDoubleColon
  | -- | @∷@: @::@ but Unicode
    TkUniDoubleColon
  | -- | @->@: function type
    TkRightArrow
  | -- | @→@: @->@ but Unicode
    TkUniRightArrow
  | -- | @,@: common separator
    TkComma
  | -- | @_@: wildcard pattern
    TkUnderscore
  | -- | A valid symbol formed from any non-space character
    TkSymbol Text
  | -- | Any number-like form
    TkNumber Text
  | -- | Any character-like enclosed in @'@
    TkCharacter Text
  | -- | A sequence of characters enclosed in @"@
    TkString Text
  deriving (Show, Eq, Ord)
