{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Language.Zilch.Typecheck.Core.Eval (implicit, explicit, module Export) where

import Language.Zilch.Typecheck.Core.Internal as Export (Spine, Value (..), MetaEntry (..), Name, Environment, Closure (..), DeBruijnLvl (..), Implicitness)

explicit, implicit :: Implicitness
explicit = True
implicit = False
