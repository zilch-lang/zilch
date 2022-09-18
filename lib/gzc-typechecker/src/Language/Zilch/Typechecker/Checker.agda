{-# OPTIONS --allow-unsolved-metas #-}

module Language.Zilch.Typechecker.Checker where

open import Data.Located 
import Language.Zilch.Typechecker.Foreign as AST
import Language.Zilch.Typechecker.Core as TAST
open import Language.Zilch.Typechecker.Core using (Environment)
open import Language.Zilch.Typechecker.Elaborator.Class
open import Language.Zilch.Typechecker.Context
open import Language.Zilch.Typechecker.Checker.TopLevel using (checkTopLevel)
open import Language.Zilch.Typechecker.Usage using (UsageRecord; union)
import Language.Zilch.Typechecker.Usage as Usage
open import Language.Zilch.Typechecker.Simplifier
open import Language.Zilch.Typechecker.Errors

open import Prelude.Monad
open import Prelude.Applicative
open import Control.Monad.Transformer using (lift)
open import Prelude.List using (List; []; _∷_)
open import Prelude.Function using (_$_)
open import Prelude.Product using (Exist; _×_; _,_)
open import Prelude.Unit
open import Prelude.Vec using (Vec)
import Prelude.Vec as Vec

private 
  {-# TERMINATING #-}
  checkProgram′ : ∀ {n} → Context n → Located AST.Module → Elaborator (Exist Context × Located TAST.Module × UsageRecord)
  checkProgram′ {n} ctx (AST.Mod [] at p) = return ((n , ctx) , (TAST.Mod [] at p) , Usage.empty)
  checkProgram′ {n} ctx (AST.Mod (t ∷ ts) at p) = do 
    b , (n , ctx) , u₁ ← checkTopLevel ctx t 
    ctx , (TAST.Mod bs at p₁) , u₂ ← checkProgram′ {n = n} ctx (AST.Mod ts at p)
    return $ ctx , TAST.Mod (b ∷ bs) at p , union u₁ u₂

  checkAllDefined : ∀ {n} → Vec Binding n → Environment n → Elaborator ⊤′ 
  checkAllDefined Vec.[] Vec.[] = return tt
  checkAllDefined (def _ (x at p) _ _ Vec.∷ _) ((TAST.V-undef at _) Vec.∷ _) =
    liftE $ throwError $ UndefinedValueBinding x p
  checkAllDefined (_ Vec.∷ types) (_ Vec.∷ env) = checkAllDefined types env

checkProgram : ∀ {n} → Context n → Located AST.Module → Elaborator (Located TAST.Module)
checkProgram ctx mod = do
  (_ , ctx) , mod , us ← checkProgram′ ctx mod 
  
  -- check that all 'val' bindings have definitions
  checkAllDefined (ctx .types) (ctx .env)
  -- TODO: check mutually recursive value occurrences
  
  inlineAllMetavars mod 
