{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Pretty.AST where

import Data.Located (Located ((:@)), unLoc)
import Language.Zilch.Syntax.Core.AST
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))
import Prettyprinter (Doc, Pretty (pretty), align, braces, comma, concatWith, emptyDoc, enclose, hardline, indent, line, parens, space, surround, vsep)

instance Pretty (Located Module) where
  pretty (Mod defs :@ _) =
    vsep (pretty <$> defs)

instance Pretty (Located TopLevel) where
  pretty (TopLevel isPublic def :@ _) =
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
  pretty (Import isOpened mod item :@ _) =
    (if isOpened then "open" <> space else "")
      <> "import"
      <> space
      <> concatWith (surround "∷") (pretty . unLoc <$> mod)
      <> space
      <> concatWith (surround "∷") (pretty . unLoc <$> item)

instance Pretty (Located Parameter) where
  pretty (Parameter False (W :@ _) ("_" :@ _) ty :@ _) =
    pretty ty
  pretty (Parameter isImplicit mult name ty :@ _) =
    (if isImplicit then enclose "{" "}" else enclose "(" ")") $
      pretty mult
        <> space
        <> pretty (unLoc name)
        <> space
        <> ":"
        <> space
        <> pretty ty

instance Pretty (Located Multiplicity) where
  pretty (Unrestricted :@ _) = "ω"
  pretty (Linear :@ _) = "1"
  pretty (Erased :@ _) = "0"

instance Pretty (Located Expression) where
  pretty (EType :@ _) = "type"
  pretty (EInteger val suffix :@ _) =
    pretty (unLoc val)
      <> pretty suffix
  pretty (ECharacter c :@ _) = enclose "'" "'" . pretty $ unLoc c
  pretty (EIdentifier id :@ _) = pretty $ unLoc id
  pretty (ELam param ret :@ _) =
    "λ"
      <> space
      <> pretty param
      <> space
      <> "⇒"
      <> space
      <> pretty ret
  pretty (ELocal def ret :@ _) =
    pretty def
      <> line
      <> pretty ret
  pretty (EApplication fun isImp arg :@ _) =
    pretty fun
      <> (if isImp then braces else parens) (pretty arg)
  pretty (EHole _ :@ _) = "_"
  pretty (EPi param val :@ _) = prettyDependent param "→" val
  pretty (EMultiplicativeProduct param val :@ _) = prettyDependent param "⊗" val
  pretty (EAdditiveProduct param val :@ _) = prettyDependent param "&" val
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
  pretty (EAdditiveTupleAccess e n :@ _) =
    pretty e
      <> "∷"
      <> pretty n
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

prettyDependent :: Located Parameter -> Doc ann -> Located Expression -> Doc ann
prettyDependent param op val =
  pretty param
    <> space
    <> op
    <> space
    <> pretty val

instance Pretty IntegerSuffix where
  pretty SuffixS8 = "s8"
  pretty SuffixS16 = "s16"
  pretty SuffixS32 = "s32"
  pretty SuffixS64 = "s64"
  pretty SuffixU8 = "u8"
  pretty SuffixU16 = "u16"
  pretty SuffixU32 = "u32"
  pretty SuffixU64 = "u64"
