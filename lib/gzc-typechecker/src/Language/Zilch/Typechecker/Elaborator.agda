module Language.Zilch.Typechecker.Elaborator where

open import Data.Located using (Located)
import Language.Zilch.Typechecker.Foreign as AST
import Language.Zilch.Typechecker.Core as TAST
open import Language.Zilch.Typechecker.Errors using (ElabError; ElabWarning)
open import Language.Zilch.Typechecker.Checker using (checkProgram)
open import Language.Zilch.Typechecker.Context.Defaults
open import Language.Zilch.Typechecker.Elaborator.Class using (runElaborator)

open import Data.HsTuple using (_×′_; ×→×′)

open import Prelude.List using (List)
open import Prelude.Sum using (Either; mapRight)
open import Prelude.Product using (_×_; fst)
open import Prelude.Function using (_∘_)

elabProgram : Located AST.Module → Either ElabError (Located TAST.Module × List ElabWarning)
elabProgram = mapRight fst ∘ runElaborator default-metavars ∘ checkProgram default-context 

elabProgram′ : Located AST.Module → Either ElabError (Located TAST.Module ×′ List ElabWarning)
elabProgram′ = mapRight ×→×′ ∘ elabProgram
{-# COMPILE GHC elabProgram′ as elabProgram #-}