{-# LANGUAGE DerivingVia #-}

module Language.Zilch.Typecheck.Core.AST (Module (..), TopLevel (..), MetaAttribute (..), CallingConvention (..), module Export) where

import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.Internal as Export (BuiltinType (..), DeBruijnIdx (..), Definition (..), Expression (..), Parameter (..), Path (..))

data Module
  = Mod [Located TopLevel]
  deriving (Show)

data TopLevel
  = TopLevel
      [Located MetaAttribute]
      -- ^ Meta attributes
      Bool
      -- ^ Is it public?
      (Located Definition)
  deriving (Show)

data MetaAttribute
  = Foreign CallingConvention (Located Text)
  | Inline
  deriving (Show)

data CallingConvention
  = CCall
  deriving (Show)
