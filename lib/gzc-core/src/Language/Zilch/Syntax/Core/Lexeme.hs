module Language.Zilch.Syntax.Core.Lexeme (Token (..)) where

import Data.Text (Text)

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
  | -- | @=>@: lambda expression separator
    TkDoubleRightArrow
  | -- | @⇒@: @=>@ but Unicode
    TkUniDoubleRightArrow
  | -- | @true@
    TkTrue
  | -- | @false@
    TkFalse
  | -- | @forall@: universal type quantifier
    TkForall
  | -- | @∀@: @forall@ but Unicode
    TkUniForall
  | -- | @exists@: existential type quantifier
    TkExists
  | -- | @∃@: @exists@ but Unicode
    TkUniExists
  | -- | @,@: common separator
    TkComma
  | -- | @_@: wildcard pattern
    TkUnderscore
  | -- | @?@: typed holes
    TkQuestionMark
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
  | -- | Multiline comment, enclosed by @/-@ and  @-/@
    TkMultilineComment Text
  deriving (Show, Eq, Ord)
