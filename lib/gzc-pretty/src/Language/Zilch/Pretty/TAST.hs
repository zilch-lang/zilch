{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.TAST where

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

instance Pretty (Located Parameter) where
  pretty (Parameter isImplicit name ty :@ _) =
    (if isImplicit then enclose "{" "}" else enclose "(" ")") $
      pretty (unLoc name)
        <> space
        <> ":"
        <> space
        <> pretty ty

instance Pretty (Located Expression) where
  pretty (EType :@ _) = "type"
  pretty (EInteger val :@ _) = pretty $ unLoc val
  pretty (ECharacter c :@ _) = enclose "'" "'" . pretty $ unLoc c
  pretty (EIdentifier (Idx id :@ _) :@ _) = "arg_" <> pretty id
  pretty (ELam ret :@ _) =
    "λ"
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
  pretty (EPi param val :@ _) =
    pretty param
      <> space
      <> "→"
      <> space
      <> pretty val
  pretty (EMeta i :@ _) = "?" <> pretty (unLoc i)
  pretty (EInsertedMeta i bds :@ _) = "?" <> pretty (unLoc i) <> goBds bds
    where
      goBds [] = emptyDoc
      goBds (Bound : bds) = space <> "_" <> goBds bds
      goBds (Defined : bds) = goBds bds
