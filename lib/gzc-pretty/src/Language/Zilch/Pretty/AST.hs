{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.AST where

import Data.Located (Located ((:@)), unLoc)
import Language.Zilch.Syntax.Core.AST
import Prettyprinter (Pretty (pretty), emptyDoc, enclose, hsep, indent, line, space, vsep)

instance Pretty (Located Module) where
  pretty (Mod _ defs :@ _) =
    vsep (pretty <$> defs)

instance Pretty (Located TopLevel) where
  pretty (TopLevel isPublic def :@ _) =
    (if isPublic then "public" <> line else emptyDoc)
      <> pretty def

instance Pretty (Located Definition) where
  pretty (Let isRec name implicits explicits returnTy val :@ _) =
    (if isRec then "rec" else "let")
      <> indent
        2
        ( space
            <> pretty (unLoc name)
            <> space
            <> hsep (pretty <$> implicits)
            <> line
            <> hsep (pretty <$> explicits)
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
  pretty (EForall implicits explicits ret :@ _) =
    "∀"
      <> space
      <> hsep (pretty <$> implicits)
      <> space
      <> hsep (pretty <$> explicits)
      <> ","
      <> space
      <> pretty ret
  pretty (EExists implicits explicits ret :@ _) =
    "∃"
      <> space
      <> hsep (pretty <$> implicits)
      <> space
      <> hsep (pretty <$> explicits)
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
  pretty (ELam params ret :@ _) =
    "λ"
      <> space
      <> hsep (pretty <$> params)
      <> space
      <> "→"
      <> space
      <> pretty ret
  pretty (ELet def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun implicits explicits :@ _) =
    pretty fun
      <> line
      <> indent 2 (hsep $ pretty <$> implicits)
      <> line
      <> indent 2 (hsep $ pretty <$> explicits)
  pretty (EHole :@ _) = "?"
