module Language.Zilch.Typechecker.Context.Defaults where

open import Language.Zilch.Typechecker.Context using (Context; empty)
open import Language.Zilch.Typechecker.Metavars using (MetaContext; mapping)

import Prelude.Vec as Vec
open import Prelude.Equality using (refl)

default-context : Context 0
default-context = empty

default-metavars : MetaContext 0 
default-metavars = record { mapping = Vec.[] }