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
  pretty (EIdentifier (name :@ _) idx :@ _) = pretty name -- <> "@" <> pretty (fromIntegral @_ @Integer idx)
  pretty (ELam name ret :@ _) =
    "λ"
      <> space
      <> pretty name
      <> space
      <> "⇒"
      <> line
      <> flatAlt (indent 2 (pretty ret)) (pretty ret)
  pretty (ELet def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun isImplicit arg :@ _) =
    pretty fun
      <> (if isImplicit then braces else parens) (pretty arg)
  pretty (EPi param val :@ _) = prettyDependent param "→" val
  pretty (EMultiplicativeProduct param val :@ _) = prettyDependent param "⊗" val
  pretty (EAdditiveProduct param val :@ _) = prettyDependent param "&" val
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
  pretty (EMultiplicativePair e1 e2 :@ _) =
    enclose "(" ")" $
      pretty e1
        <> comma
        <> space
        <> pretty e2
  pretty (EAdditivePair e1 e2 :@ _) =
    enclose "⟨" "⟩" $
      pretty e1
        <> comma
        <> space
        <> pretty e2
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
  pretty (EMultiplicativePairElim z mult x y m n :@ _) =
    "let"
      <> space
      <> pretty mult
      <> space
      <> parens (pretty (unLoc x) <> comma <> space <> pretty (unLoc y))
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
  pretty (ERecordAccess r x :@ _) =
    parensIfNeeded r
      <> "∷"
      <> pretty (unLoc x)
    where
      parensIfNeeded e@(EIdentifier _ _ :@ _) = pretty e
      parensIfNeeded e@(ERecordLiteral _ :@ _) = pretty e
      parensIfNeeded e@(ERecordAccess _ _ :@ _) = pretty e
      parensIfNeeded e = parens (pretty e)

prettyDependent :: Located Parameter -> Doc ann -> Located Expression -> Doc ann
prettyDependent param op val =
  pretty param
    <> space
    <> op
    <> space
    <> pretty val

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
