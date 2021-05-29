{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.Tokens (pretty) where

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Language.Zilch.Core.Tokens (Token(..))
import qualified Data.Text as Text

instance Pretty Token where
  pretty Forall            = text "forall"
  pretty UniForall         = text "∀"
  pretty Def               = text "def"
  pretty Enum              = text "enum"
  pretty Record            = text "record"
  pretty Class             = text "class"
  pretty Impl              = text "impl"
  pretty Where             = text "where"
  pretty Do                = text "do"
  pretty Type              = text "type"
  pretty Case              = text "case"
  pretty Of                = text "of"
  pretty Module            = text "module"
  pretty Fn                = text "fn"
  pretty Foreign           = text "foreign"
  pretty As                = text "as"
  pretty Open              = text "open"
  pretty Import            = text "import"
  pretty Export            = text "export"
  pretty Perm              = text "perm"
  pretty If                = text "if"
  pretty Then              = text "then"
  pretty Else              = text "else"
  pretty Pattern           = text "pattern"
  pretty ColonEquals       = text ":="
  pretty UniColonEquals    = text "≔"
  pretty LeftArrow         = text "<-"
  pretty UniLeftArrow      = text "←"
  pretty RightArrow        = text "->"
  pretty UniRightArrow     = text "→"
  pretty LessColon         = text "<:"
  pretty Underscore        = text "_"
  pretty UniUnderscore     = text "·"
  pretty Dot               = text "."
  pretty Question          = text "?"
  pretty LParen            = text "("
  pretty RParen            = text ")"
  pretty LBrack            = text "["
  pretty RBrack            = text "]"
  pretty LBrace            = text "{"
  pretty RBrace            = text "}"
  pretty Comma             = text ","
  pretty Colon             = text ":"
  pretty Hash              = text "#"
  pretty (Identifier i)    = text (Text.unpack i)
  pretty (InlineComment c) = text "-- " <> text (Text.unpack c)
  pretty (Integer i)       = text (Text.unpack i)
  pretty (Float f)         = text (Text.unpack f)
  pretty (String s)        = text (Text.unpack s)
  pretty (Character c)     = text (Text.unpack c)