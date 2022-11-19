{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.TAST where

import Data.Foldable (fold)
import Data.Functor ((<&>))
import Data.Located (Located ((:@)), unLoc)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Typecheck.Core.AST
import Language.Zilch.Typecheck.Core.Multiplicity
import Prettyprinter (Doc, Pretty (pretty), align, braces, colon, comma, concatWith, dquote, emptyDoc, enclose, flatAlt, group, hardline, indent, line, lparen, parens, rparen, space, surround, vsep)

instance Pretty (Located Module) where
  pretty (Mod defs :@ _) =
    vsep (pretty <$> defs)

instance Pretty (Located TopLevel) where
  pretty (TopLevel attrs isPublic def :@ _) =
    "#attributes"
      <> lparen
      <> prettyAttrs attrs
      <> (if not (null attrs) then hardline else emptyDoc)
      <> rparen
      <> hardline
      <> (if isPublic then "public" <> space else emptyDoc)
      <> pretty def
      <> hardline
    where
      prettyAttrs attrs = fold $ attrs <&> \a -> hardline <> indent 2 (pretty a) <> comma

instance Pretty (Located MetaAttribute) where
  pretty (Inline :@ _) = "inline"
  pretty (Foreign conv (name :@ _) :@ _) =
    "foreign"
      <> lparen
      <> "import"
      <> comma
      <> space
      <> pretty' conv
      <> comma
      <> space
      <> dquote
      <> pretty name
      <> dquote
      <> rparen
    where
      pretty' CCall = "c"

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
  pretty (Val usage name typ :@ _) =
    "val"
      <> space
      <> pretty usage
      <> space
      <> pretty (unLoc name)
      <> space
      <> ":"
      <> space
      <> pretty typ
  pretty (External mult name typ _ mod path :@ _) =
    "external"
      <> space
      <> pretty mult
      <> space
      <> pretty (unLoc name)
      <> space
      <> ":"
      <> space
      <> pretty typ
      <> line
      <> indent
        2
        ( "from"
            <> space
            <> pretty' mod
            <> space
            <> "("
            <> pretty path
            <> ")"
        )
    where
      pretty' = pretty . Text.intercalate "∷" . fmap unLoc

instance Pretty (Located Parameter) where
  pretty (Parameter isImplicit usage name ty :@ _) =
    (if isImplicit then enclose "{" "}" else enclose "(" ")") $
      pretty usage
        <> space
        <> pretty (unLoc name)
        <> space
        <> ":"
        <> space
        <> group (pretty ty)

instance Pretty (Located Expression) where
  pretty (EType :@ _) = "type"
  pretty (EInteger val ty :@ _) = pretty (unLoc val) <> pretty ty
  pretty (ECharacter c :@ _) = enclose "'" "'" . pretty $ unLoc c
  pretty (EIdentifier (name :@ _) idx ty :@ _) =
    parens $
      pretty name
        <> space
        <> colon
        <> space
        <> pretty ty
  pretty (ELam name ty ret :@ _) =
    "λ"
      <> space
      <> pretty name
      <> space
      <> colon
      <> space
      <> pretty ty
      <> space
      <> "⇒"
      <> line
      <> flatAlt (indent 2 (pretty ret)) (pretty ret)
  pretty (ELet def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun isImplicit ty arg :@ _) =
    pretty fun
      <> line
      <> indent 2 ((if isImplicit then braces else parens) (pretty arg <> space <> colon <> space <> pretty ty))
  pretty (EPi param ty val :@ _) = prettyDependent param "→" val ty
  pretty (EMultiplicativeProduct param ty val :@ _) = prettyDependent param "⊗" val ty
  pretty (EAdditiveProduct param ty val :@ _) = prettyDependent param "&" val ty
  pretty (EInsertedMeta m path :@ _) =
    "?"
      <> pretty m
      <> prettyBinding path
    where
      prettyBinding Here = ""
      prettyBinding (Bind p _ (name :@ _) _) = prettyBinding p <> space <> pretty name
      prettyBinding (Define p _ _ _ _) = prettyBinding p
  pretty (EMeta m :@ _) =
    "?" <> pretty m
  pretty (EBuiltin ty :@ _) =
    pretty ty
  pretty (EBoolean bool :@ _) =
    if bool then "true" else "false"
  pretty (EIfThenElse cond t ty1 e ty2 :@ _) =
    align $
      "if"
        <> space
        <> pretty cond
        <> line
        <> "then"
        <> space
        <> parens (pretty t <> space <> colon <> space <> pretty ty1)
        <> line
        <> "else"
        <> space
        <> parens (pretty e <> space <> colon <> space <> pretty ty2)
  pretty (EMultiplicativePair e1 t1 e2 t2 :@ _) =
    parens $
      pretty e1
        <> space
        <> colon
        <> space
        <> pretty t1
        <> comma
        <> space
        <> pretty e2
        <> space
        <> colon
        <> space
        <> pretty t2
  pretty (EAdditivePair e1 t1 e2 t2 :@ _) =
    enclose "⟨" "⟩" $
      pretty e1
        <> space
        <> colon
        <> space
        <> pretty t1
        <> comma
        <> space
        <> pretty e2
        <> space
        <> colon
        <> space
        <> pretty t2
  pretty (EAdditiveUnit :@ _) = "⟨" <> "⟩"
  pretty (EMultiplicativeUnit :@ _) = "(" <> ")"
  pretty (EOne :@ _) = "𝟏"
  pretty (ETop :@ _) = "⊤"
  pretty (EFst e :@ _) =
    "FST"
      <> space
      <> pretty e
  pretty (ESnd e :@ _) =
    "SND"
      <> space
      <> pretty e
  pretty (EMultiplicativePairElim z mult x tx y ty m n :@ _) =
    "let"
      <> space
      <> pretty mult
      <> space
      <> parens
        ( pretty (unLoc x)
            <> space
            <> colon
            <> space
            <> pretty tx
            <> comma
            <> space
            <> pretty (unLoc y)
            <> space
            <> colon
            <> pretty ty
        )
      <> maybe emptyDoc (\z -> space <> "as" <> space <> pretty (unLoc z)) z
      <> space
      <> "≔"
      <> space
      <> pretty m
      <> hardline
      <> pretty n
  pretty (EMultiplicativeUnitElim z mult m n :@ _) =
    "let"
      <> space
      <> pretty mult
      <> space
      <> parens emptyDoc
      <> maybe emptyDoc (\z -> space <> "as" <> space <> pretty (unLoc z)) z
      <> space
      <> "≔"
      <> space
      <> pretty m
      <> hardline
      <> pretty n
  pretty (EComposite fields :@ _) =
    "'"
      <> align
        ( "{"
            <> space
            <> concatWith (surround $ line <> "," <> space) (prettyField <$> fields)
            <> space
            <> "}"
        )
    where
      prettyField (p, x, t) =
        "val"
          <> space
          <> pretty p
          <> space
          <> pretty (unLoc x)
          <> space
          <> colon
          <> space
          <> pretty t
  pretty (EModule fields :@ _) =
    "MODULE"
      <> space
      <> align
        ( "{"
            <> space
            <> concatWith (surround $ line <> "," <> space) (prettyField <$> Map.toList fields)
            <> space
            <> "}"
        )
    where
      prettyField (x, (p, t)) =
        pretty p
          <> space
          <> pretty (unLoc x)
          <> space
          <> colon
          <> space
          <> pretty t
  pretty (ERecordLiteral fields :@ _) =
    "@"
      <> align
        ( "{"
            <> space
            <> concatWith (surround $ line <> "," <> space) (prettyField <$> fields)
            <> space
            <> "}"
        )
    where
      prettyField (p, x, t, e) =
        "let"
          <> space
          <> pretty p
          <> space
          <> pretty (unLoc x)
          <> space
          <> colon
          <> space
          <> pretty t
          <> space
          <> indent 2 ("≔" <> space <> pretty e)
  pretty (ERecordAccess r tr x :@ _) =
    parens (pretty r <> space <> colon <> space <> pretty tr)
      <> line
      <> indent 2 ("∷" <> pretty (unLoc x))

prettyDependent :: Located Parameter -> Doc ann -> Located Expression -> Located Expression -> Doc ann
prettyDependent param op val ty =
  pretty param
    <> space
    <> op
    <> space
    <> parens
      ( pretty val
          <> space
          <> colon
          <> space
          <> pretty ty
      )

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
