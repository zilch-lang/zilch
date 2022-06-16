{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.TAST where

import Data.Foldable (fold)
import Data.List (intersperse)
import Data.Located (Located ((:@)), unLoc)
import Language.Zilch.Typecheck.Core.AST
import Prettyprinter (Pretty (pretty), emptyDoc, enclose, hardline, indent, line, parens, space, vsep)

instance Pretty (Located Module) where
  pretty (Mod defs :@ _) =
    vsep (pretty <$> defs)

instance Pretty (Located TopLevel) where
  pretty (TopLevel _ isPublic def :@ _) =
    (if isPublic then "public" <> space else emptyDoc)
      <> pretty def
      <> hardline

instance Pretty (Located Definition) where
  pretty (Let isRec name typ val :@ _) =
    (if isRec then "rec" else "let")
      <> space
      <> pretty (unLoc name)
      <> line
      <> indent
        2
        ( ":"
            <> space
            <> pretty typ
            <> line
            <> "≔"
            <> line
            <> line
            <> pretty val
        )
  pretty (LetMeta idx val :@ _) =
    "let?"
      <> space
      <> pretty idx
      <> space
      <> "≔"
      <> space
      <> maybe "?" prettyValue val
    where
      prettyValue val = hardline <> indent 2 (pretty val)

instance Pretty (Located Parameter) where
  pretty (Parameter isImplicit usage name ty :@ _) =
    (if isImplicit then enclose "{" "}" else enclose "(" ")") $
      maybe "ω" (pretty . unLoc) usage
        <> space
        <> pretty (unLoc name)
        <> space
        <> ":"
        <> space
        <> pretty ty

instance Pretty (Located Expression) where
  pretty (EType :@ _) = "type"
  pretty (EInteger val :@ _) = pretty $ unLoc val
  pretty (ECharacter c :@ _) = enclose "'" "'" . pretty $ unLoc c
  pretty (EIdentifier (name :@ _) _ :@ _) = pretty name
  pretty (ELam name ret :@ _) =
    "λ"
      <> space
      <> pretty name
      <> space
      <> "→"
      <> line
      <> indent 2 (pretty ret)
  pretty (ELet def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun arg :@ _) =
    pretty fun
      <> space
      <> parens (pretty arg)
  pretty (EPi param val :@ _) =
    pretty param
      <> space
      <> "→"
      <> space
      <> pretty val
  pretty (EInsertedMeta m bds :@ _) =
    "?"
      <> pretty m
      <> fold (prettyBinding <$> reverse bds)
    where
      prettyBinding (Bound name) = space <> pretty name
      prettyBinding (Defined _) = ""
  pretty (EMeta m :@ _) =
    "?" <> pretty m
  pretty (EUnknown :@ _) =
    "???"
