module Language.Zilch.Typechecker.Metavars.Fresh where 

open import Data.Located
open import Language.Zilch.Typechecker.Elaborator.Class 
open import Language.Zilch.Typechecker.Core 
import Language.Zilch.Typechecker.Foreign.AST as AST 
open import Language.Zilch.Typechecker.Context using (Context; env; path; lvl)
open import Language.Zilch.Typechecker.Normaliser.Eval using ([_]↝_)
open import Language.Zilch.Typechecker.Normaliser.Quote using (⟦_,_⟧)
open import Language.Zilch.Typechecker.Metavars

open import Prelude.Nat using (Nat; suc; _-N_)
open import Prelude.Product using (_,_)
open import Prelude.Function using (_$_; _∘_)
open import Prelude.Vec using (_∷_)
open import Prelude.Bool using (false; true)

closeTy : ∀ {m} → DeBruijnLvl → Path m → Located Expression → Elaborator (Located Expression)
closeTy _ Here e = return e 
closeTy lvl (Bind path m x a) e@(_ at p) = do
  a ← ⟦ lvl , a ⟧
  closeTy (lvl -N 1) path $ (E-Π (Param Explicit m x a at p) , e) at p
closeTy lvl (Define path m x a b) e@(_ at p) = do 
  a ← ⟦ lvl , a ⟧ 
  b ← ⟦ lvl , b ⟧
  closeTy (lvl -N 1) path $ E-let (D-let false m x a b at p) true e at p

-- | Insert a new meta variable into the context and return its index.
mk-meta : ∀ {m} → Located Multiplicity → Located Value → Path m → Located AST.HoleLoc → Elaborator Nat 
mk-meta {m} mult τ path loc = do 
  n , ctx ← liftS get 
  let n′ = suc n 
  liftS $ put $ n′ , record { mapping = (m , Unsolved (mult -pos) τ , path , loc) ∷ ctx .mapping }
  return n

-- | Generate a new metavariable with a given multiplicity and type.
fresh-meta : ∀ {n} → Context n → Located Multiplicity → Located Value → Position → AST.HoleLoc → Elaborator Expression
fresh-meta Γ mult τ p loc = do 
  τ-closed ← ([ Γ .env ]↝_) =<< closeTy (Γ .lvl) (Γ .path) =<< ⟦ Γ .lvl , τ ⟧
  m ← mk-meta mult τ-closed (Γ .path) (loc at p)
  return $ E-insmeta m (Γ .path) 
