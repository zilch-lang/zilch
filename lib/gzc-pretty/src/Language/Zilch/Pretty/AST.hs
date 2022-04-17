{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.AST where

import Data.Located (Located ((:@)), unLoc)
import Language.Zilch.Syntax.Core.AST
import Prettyprinter (Pretty (pretty), braces, emptyDoc, enclose, hsep, indent, line, parens, space, vsep)

instance Pretty (Located Module) where
  pretty (Mod _ defs :@ _) =
    vsep (pretty <$> defs)

instance Pretty (Located TopLevel) where
  pretty (TopLevel isPublic def :@ _) =
    (if isPublic then "public" <> line else emptyDoc)
      <> pretty def

instance Pretty (Located Definition) where
  pretty (Let isRec name params returnTy val :@ _) =
    (if isRec then "rec" else "let")
      <> indent
        2
        ( space
            <> pretty (unLoc name)
            <> line
            <> hsep (pretty <$> params)
            <> space
            <> maybe emptyDoc ((space <>) . (":" <>) . (space <>) . pretty) returnTy
            <> "≔"
            <> line
            <> pretty val
        )

instance Pretty (Located Parameter) where
  pretty (Parameter isImplicit name ty :@ _) =
    (if isImplicit then enclose "{" "}" else enclose "(" ")") $
      pretty (unLoc name)
        <> maybe emptyDoc ((":" <>) . (space <>) . pretty) ty

instance Pretty (Located Expression) where
  pretty (EType :@ _) = "type"
  pretty (EForall params ret :@ _) =
    "∀"
      <> space
      <> hsep (pretty <$> params)
      <> ","
      <> space
      <> pretty ret
  pretty (EExists params ret :@ _) =
    "∃"
      <> space
      <> hsep (pretty <$> params)
      <> ","
      <> space
      <> pretty ret
  pretty (EInteger val :@ _) = pretty $ unLoc val
  pretty (ECharacter c :@ _) = enclose "'" "'" . pretty $ unLoc c
  pretty (EIdentifier id :@ _) = pretty $ unLoc id
  pretty (EDo expr :@ _) =
    "do"
      <> line
      <> indent 2 (pretty expr)
  pretty (ELam param ret :@ _) =
    "λ"
      <> space
      <> pretty param
      <> space
      <> "→"
      <> space
      <> pretty ret
  pretty (ELet def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun arg :@ _) =
    pretty fun
      <> line
      <> indent 2 (parens $ pretty arg)
  pretty (EHole :@ _) = "?"
  pretty (EImplicit expr :@ _) = braces $ pretty expr
