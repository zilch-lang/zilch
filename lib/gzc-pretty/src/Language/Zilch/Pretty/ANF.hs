{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.ANF where

import Data.Foldable (fold)
import Data.Functor ((<&>))
import Data.Located (Located ((:@)), unLoc)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Language.Zilch.Pretty.TAST ()
import Language.Zilch.Typecheck.Core.Multiplicity
import Language.Zilch.Typecheck.ANF
import Prettyprinter (Doc, Pretty (pretty), align, braces, colon, comma, concatWith, dquote, emptyDoc, enclose, flatAlt, group, hardline, indent, line, lparen, parens, rparen, space, surround, vsep)

instance Pretty (Located Module) where
  pretty (Module defs :@ _) =
    vsep (pretty <$> defs)

instance Pretty (Located TopLevel) where
  pretty (TopLevel attrs def :@ _) =
    "#attributes"
      <> lparen
      <> prettyAttrs attrs
      <> (if not (null attrs) then hardline else emptyDoc)
      <> rparen
      <> hardline
      <> pretty def
      <> hardline
    where
      prettyAttrs attrs = fold $ attrs <&> \a -> hardline <> indent 2 (pretty a) <> comma

instance Pretty (Located Definition) where
  pretty (Let isRec usage name typ val :@ _) =
    (if isRec then "rec" else "let")
      <> space
      <> pretty usage
      <> space
      <> pretty' name
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
    where
      pretty' = pretty . Text.intercalate "∷" . fmap unLoc
  -- pretty (Val usage name typ :@ _) =
  --   "val"
  --     <> space
  --     <> pretty usage
  --     <> space
  --     <> pretty (unLoc name)
  --     <> space
  --     <> ":"
  --     <> space
  --     <> pretty typ

instance Pretty (Located Parameter) where
  pretty (Parameter usage name ty :@ _) =
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
  pretty (EIdentifier name :@ _) = pretty' name -- <> "@" <> pretty (fromIntegral @_ @Integer idx)
    where
      pretty' = pretty . Text.intercalate "∷" . fmap unLoc
  pretty (ELam name ret :@ _) =
    "λ"
      <> space
      <> parens (concatWith (surround comma) $ pretty <$> name)
      <> space
      <> "⇒"
      <> line
      <> flatAlt (indent 2 (pretty ret)) (pretty ret)
  pretty (ELet def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun arg :@ _) =
    pretty fun <> parens (concatWith (surround comma) $ pretty <$> arg)
  pretty (EPi param val :@ _) = prettyDependent param "→" val
  pretty (EMultiplicativeProduct param val :@ _) = prettyDependent param "⊗" val
  pretty (EAdditiveProduct param val :@ _) = prettyDependent param "&" val
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
  pretty (EMultiplicativePair es :@ _) =
    parens $ concatWith (surround comma) $ pretty <$> es
  pretty (EAdditivePair es :@ _) =
    enclose "⟨" "⟩" $ concatWith (surround comma) $ pretty <$> es
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
  pretty (EMultiplicativePairElim z mult xs m n :@ _) =
    "let"
      <> space
      <> pretty mult
      <> space
      <> parens (concatWith (surround comma) $ pretty . unLoc <$> xs)
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
          <> "≔"
          <> space
          <> pretty e
  pretty (ERecordAccess r x :@ _) =
    parensIfNeeded r
      <> "∷"
      <> pretty (unLoc x)
    where
      parensIfNeeded e@(EIdentifier _ :@ _) = pretty e
      parensIfNeeded e@(ERecordLiteral _ :@ _) = pretty e
      parensIfNeeded e@(ERecordAccess _ _ :@ _) = pretty e
      parensIfNeeded e = parens (pretty e)

prettyDependent :: [Located Parameter] -> Doc ann -> Located Expression -> Doc ann
prettyDependent param op val =
  parens (concatWith (surround comma) $ pretty <$> param)
    <> space
    <> op
    <> space
    <> pretty val
