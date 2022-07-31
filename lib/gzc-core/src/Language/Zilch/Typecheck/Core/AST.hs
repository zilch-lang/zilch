{-# LANGUAGE DerivingVia #-}

module Language.Zilch.Typecheck.Core.AST (Module (..), TopLevel (..), module Export) where

import Data.Located (Located)
import Language.Zilch.Typecheck.Core.Internal as Export (Parameter (..), Expression (..), Definition (..), DeBruijnIdx (..), BuiltinType (..), Path (..))

data Module
  = Mod [Located TopLevel]
  deriving (Show)

data TopLevel
  = TopLevel
      [()]
      -- ^ For future use (maybe)
      Bool
      -- ^ Is it public?
      (Located Definition)
  deriving (Show)
