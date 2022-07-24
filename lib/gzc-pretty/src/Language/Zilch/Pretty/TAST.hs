{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.TAST where

import Data.Foldable (fold)
import Data.Located (Located ((:@)), unLoc)
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Typecheck.Core.AST
import Prettyprinter (Pretty (pretty), align, braces, emptyDoc, enclose, hardline, indent, line, parens, space, vsep)

instance Pretty (Located Module) where
  pretty (Mod defs :@ _) =
    vsep (pretty <$> defs)

instance Pretty (Located TopLevel) where
  pretty (TopLevel _ isPublic def :@ _) =
    (if isPublic then "public" <> space else emptyDoc)
      <> pretty def
      <> hardline

instance Pretty (Located Definition) where
  pretty (Let isRec usage name typ val :@ _) =
    (if isRec then "rec" else "let")
      <> space
      <> pretty usage
      <> space
      <> pretty (unLoc name)
      <> space
      <> ":"
      <> space
      <> pretty typ
      <> line
      <> indent
        2
        ( "≔"
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
      pretty usage
        <> space
        <> pretty (unLoc name)
        <> space
        <> ":"
        <> space
        <> pretty ty

instance Pretty (Located Expression) where
  pretty (EType :@ _) = "type"
  pretty (EInteger val ty :@ _) = pretty (unLoc val) <> pretty ty
  pretty (ECharacter c :@ _) = enclose "'" "'" . pretty $ unLoc c
  pretty (EIdentifier (name :@ _) _ :@ _) = pretty name
  pretty (ELam name ret :@ _) =
    "λ"
      <> space
      <> pretty name
      <> space
      <> "⇒"
      <> line
      <> indent 2 (pretty ret)
  pretty (ELet def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun isImplicit arg :@ _) =
    pretty fun
      <> (if isImplicit then braces else parens) (pretty arg)
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
  pretty (EBuiltin ty :@ _) =
    pretty ty
  pretty (EUnknown :@ _) =
    "???"
  pretty (EBoolean bool :@ _) =
    if bool then "true" else "false"
  pretty (EIfThenElse cond t e :@ _) =
    align $
      "if"
        <> space
        <> pretty cond
        <> line
        <> "then"
        <> space
        <> pretty t
        <> line
        <> "else"
        <> space
        <> pretty e

instance Pretty BuiltinType where
  pretty TyU64 = "u64"
  pretty TyU32 = "u32"
  pretty TyU16 = "u16"
  pretty TyU8 = "u8"
  pretty TyS64 = "s64"
  pretty TyS32 = "s32"
  pretty TyS16 = "s16"
  pretty TyS8 = "s8"
  pretty TyBool = "bool"
