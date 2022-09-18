module Language.Zilch.Typechecker.Normaliser.Quote where

open import Data.Located
open import Language.Zilch.Typechecker.Core using (Value; Expression; DeBruijnLvl; Spine; DeBruijnIdx)
import Language.Zilch.Typechecker.Core as TAST
open import Language.Zilch.Typechecker.Elaborator.Class
open import Language.Zilch.Typechecker.Normaliser.Eval using (⇓_; open-and-eval)
open import Language.Zilch.Typechecker.Errors

import Prelude.List as List using (_∷_; [])
open import Prelude.Product using (_,_)
open import Prelude.Function using (_$_)
open import Prelude.Nat using (_-N_; suc)
open import Prelude.Bool using (true; false)

level→index : DeBruijnLvl → DeBruijnLvl → DeBruijnIdx
level→index l x = l -N x -N 1

mutual 
  private 
    {-# TERMINATING #-}
    quote₁ : DeBruijnLvl → Located Value → Elaborator (Located Expression)
    quote₁ lvl val = ⇓ val >>= quote₂ lvl

    quote₂ : DeBruijnLvl → Located Value → Elaborator (Located Expression)
    quote₂ lvl (TAST.V-flexible m sp at p) = quote-spine lvl (TAST.E-meta m at p) sp p
    quote₂ lvl (TAST.V-rigid name m sp at p) =
      let idx = level→index lvl m 
       in quote-spine lvl (TAST.E-identifier name idx at p) sp p
    quote₂ lvl (TAST.V-character c at p) = return $ TAST.E-character c at p 
    quote₂ lvl (TAST.V-integer n ty at p) = return $ TAST.E-integer n ty at p 
    quote₂ lvl (TAST.V-true at p) = return $ TAST.E-boolean true at p 
    quote₂ lvl (TAST.V-false at p) = return $ TAST.E-boolean false at p 
    quote₂ lvl (TAST.V-type at p) = return $ TAST.E-type at p 
    quote₂ lvl (TAST.V-one at p) = return $ TAST.E-one at p
    quote₂ lvl (TAST.V-⊗unit at p) = return $ TAST.E-⊗unit at p 
    quote₂ lvl (TAST.V-&unit at p) = return $ TAST.E-&unit at p
    quote₂ lvl (TAST.V-⊤ at p) = return $ TAST.E-⊤ at p 
    quote₂ lvl (TAST.V-builtin ty at p) = return $ TAST.E-builtin ty at p 
    quote₂ lvl (TAST.V-fst v at p) = do 
      e ← quote₁ lvl v 
      return $ TAST.E-fst e at p 
    quote₂ lvl (TAST.V-snd v at p) = do 
      e ← quote₁ lvl v 
      return $ TAST.E-snd e at p 
    quote₂ lvl (TAST.V-λ mult name icit τ clos at p) = do 
      τ ← quote₁ lvl τ 
      x ← quote₁ (suc lvl) =<< open-and-eval (TAST.V-variable name lvl at p) clos
      return $ (TAST.E-λ (TAST.Param icit mult name τ at p) , x) at p
    quote₂ lvl (TAST.V-Π mult name icit τ clos at p) = do 
      τ ← quote₁ lvl τ 
      x ← quote₁ (suc lvl) =<< open-and-eval (TAST.V-variable name lvl at p) clos
      return $ (TAST.E-Π (TAST.Param icit mult name τ at p) , x) at p
    quote₂ lvl (TAST.V-⊗ mult name τ clos at p) = do 
      τ ← quote₁ lvl τ 
      x ← quote₁ (suc lvl) =<< open-and-eval (TAST.V-variable name lvl at p) clos
      return $ ((TAST.Param TAST.Explicit mult name τ at p) TAST.E-⊗ x) at p
    quote₂ lvl (TAST.V-& name@(_ at p₂) τ clos at p) = do 
      τ ← quote₁ lvl τ 
      x ← quote₁ (suc lvl) =<< open-and-eval (TAST.V-variable name lvl at p) clos
      return $ ((TAST.Param TAST.Explicit (TAST.^ω at p₂) name τ at p) TAST.E-& x) at p
    quote₂ lvl ((TAST.V-if cond then t else e) at p) = do 
      cond ← quote₁ lvl cond 
      t ← quote₁ lvl t 
      e ← quote₁ lvl e 
      return $ (TAST.E-if cond then t else e) at p
    quote₂ lvl ((x TAST.V-⊗, y) at p) = do 
      x ← quote₁ lvl x 
      y ← quote₁ lvl y 
      return $ (x TAST.E-⊗, y) at p 
    quote₂ lvl ((x TAST.V-&, y) at p) = do 
      x ← quote₁ lvl x 
      y ← quote₁ lvl y 
      return $ (x TAST.E-&, y) at p
    quote₂ lvl (TAST.V⟦ e ⟧ at _) = 
      -- this one is definitely a bit weird, but quoting an unspliced syntax object is basically the identity
      -- on this object.
      return e
    quote₂ lvl (TAST.V-undef at _) = liftE $ throwError $ InternalError QuotingUndefined

    quote-spine : DeBruijnLvl → Located Expression → Spine → Position → Elaborator (Located Expression)
    quote-spine _ t List.[] _ = return t 
    quote-spine lvl t ((u , i) List.∷ sp) p = do 
      t₁ ← quote₁ lvl u 
      t₂ ← quote-spine lvl t sp p 
      return $ TAST.E-application t₂ i t₁ at p

-- | Transform a term back into an abstract syntax object.
⟦_,_⟧ : DeBruijnLvl → Located Value → Elaborator (Located Expression)
⟦_,_⟧ = quote₁ 
{-# INLINE ⟦_,_⟧ #-}