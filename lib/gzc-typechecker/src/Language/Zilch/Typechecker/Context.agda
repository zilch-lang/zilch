module Language.Zilch.Typechecker.Context where

open import Data.Located
open import Language.Zilch.Typechecker.Core.Internal 
open import Language.Zilch.Typechecker.Core.Multiplicity

open import Prelude.List using (List)
open import Prelude.String using (String)
open import Prelude.Vec
open import Prelude.Nat using (Nat; suc; _-N_; lessNat)
open import Prelude.Equality
open import Prelude.Maybe using (Maybe; just; nothing)
open import Prelude.Product using (_×_; _,_; Σ; _***′_)
open import Prelude.Decidable using (yes; no)
open import Prelude.Bool
open import Prelude.Fin using (natToFin)

data Origin : Set where 
  Source : Origin
  Inserted : Origin

record Binding : Set where
  constructor def
  field 
    multiplicity : Located Multiplicity
    name : Located String
    origin : Origin
    typ : Located Value

record Context (n : Nat) : Set where
  field
    -- | The current evaluation context.
    env : Environment n
    -- | All the types known (used for lookup).
    types : Vec Binding n
    -- | The current De-Bruijn level.
    lvl : DeBruijnLvl 
    -- | The current path associated to the De-Bruijn level.
    path : Path n

    --------------- PROOFS -----------------
  
    @0 is-lvl-consistent : lvl ≡ n

-- | The empty context, containing no definition and no variable.
empty : Context 0
empty = record 
  { env = []
  ; types = []
  ; lvl = 0
  ; path = Here
  ; is-lvl-consistent = refl
  }

-- | Extend the context with a value-less variable (mostly useful to bind parameters in e.g. Π-types).
bind : ∀ {n} → Located Multiplicity → Located String → Located Value → Origin → Context n → Context (suc n)
bind m n@(_ at p) τ orig ctx = record 
  { env = V-variable n lvl at p ∷ env
  ; types = def m n orig τ ∷ types
  ; lvl = suc lvl
  ; path = Bind path m n τ
  ; is-lvl-consistent = suc $≡ is-lvl-consistent
  }
  where open Context ctx

private 
  try-replace : ∀ {n} → Environment n → Vec Binding n → Path n → (Located String × Located Value) → (Environment n × Vec Binding n × Path n)
  try-replace [] [] Here _ = [] , [] , Here
  try-replace (v ∷ env) (d ∷ types) (Bind path mult₂ name₂ τ₂) tup = 
    let env , types , path = try-replace env types path tup
      in v ∷ env , d ∷ types , Bind path mult₂ name₂ τ₂
  try-replace (v ∷ env) (d@(def _ (n₁ at _) _ _) ∷ types) (Define path mult₂ name₂ τ₂ val₂) tup@(n₀ at _ , val) 
    with n₁ == n₀ | v
  ... | yes _ | V-undef at _ = val ∷ env , d ∷ types , Define path mult₂ name₂ τ₂ val
  ... | _ | _ =
    let env , types , path = try-replace env types path tup
      in v ∷ env , d ∷ types , Define path mult₂ name₂ τ₂ val

-- | Given an environment and a name to lookup, checks whether this name is bound to an undefined value
--   (meaning it has been forward declared but not yet defined) or not.
--
--   Only bindings which are defined are taken in account.
has-undef-for : ∀ {n} → Located String → Context n → Bool 
has-undef-for name ctx = has-undef-for′ name env path 
  where 
    open Context ctx

    has-undef-for′ : ∀ {n} → Located String → Environment n → Path n → Bool
    has-undef-for′ _ [] Here = false
    has-undef-for′ name (_ ∷ env) (Bind path _ _ _) = has-undef-for′ name env path
    has-undef-for′ name@(n₁ at _) (v ∷ env) (Define path _ (n₂ at _) _ _) with n₁ == n₁ | v
    ... | yes _ | V-undef at _ = true
    ... | _ | _ = has-undef-for′ name env path

define-new-size : ∀ {n} → Located String → Context n → Nat 
define-new-size {n} name ctx = if has-undef-for name ctx then n else suc n 

-- | Extend the context with a new definition.
define : ∀ {n} → Located Multiplicity → (name : Located String) → Located Value → Located Value → (ctx : Context n) 
               → Context (define-new-size name ctx)
define mult name τ val ctx = 
  let replaced = has-undef-for name ctx
      env , types , path = try-replace env types path (name , val)
   in mk-record replaced env types lvl path is-lvl-consistent
  where
    open Context ctx 

    mk-record : ∀ {n} → (b : Bool) → Environment n → Vec Binding n → (l : DeBruijnLvl) → Path n → @0 l ≡ n 
                      → Context (if b then n else suc n)
    mk-record true env types lvl path is-lvl-consistent = record 
      { env = env
      ; types = types
      ; lvl = lvl
      ; path = path
      ; is-lvl-consistent = is-lvl-consistent
      }
    mk-record false env types lvl path is-lvl-consistent = record 
      { env = val ∷ env 
      ; types = def mult name Source τ ∷ types 
      ; lvl = suc lvl
      ; path = Define path mult name τ val
      ; is-lvl-consistent = suc $≡ is-lvl-consistent
      }
    {-# INLINE mk-record #-}

-- | Same as 'define' but does not attempt to replace a 'V-undef' within the context.
define′ : ∀ {n} → Located Multiplicity → Located String → Located Value → Located Value → Context n → Context (suc n)
define′ mult name τ val ctx = record
  { env = val ∷ env 
  ; types = def mult name Source τ ∷ types 
  ; lvl = suc lvl 
  ; path = Define path mult name τ val
  ; is-lvl-consistent = suc $≡ is-lvl-consistent
  } 
  where open Context ctx

-- | Override the multiplicity of the *first* binding with the given name in the context.
set-in-context : ∀ {n} → Context n → Located String → Located Multiplicity → Context n 
set-in-context ctx name@(n₁ at _) new-mult =
  let types , path = set-multiplicity types path
   in record ctx 
      { types = types
      ; path = path
      }
  where
    open Context ctx 

    set-multiplicity : ∀ {n} → Vec Binding n → Path n → (Vec Binding n × Path n)
    set-multiplicity [] Here = ([] , Here)
    set-multiplicity (def mult name₂@(n₂ at _) τ₁ val₁ ∷ types) path with n₁ == n₂ | path
    ... | yes _ | Define path _ name τ₂ val₂ = (def new-mult name₂ τ₁ val₁ ∷ types , Define path new-mult name τ₂ val₂)
    ... | yes _ | Bind path _ name τ₂ = (def new-mult name₂ τ₁ val₁ ∷ types , Bind path new-mult name τ₂)
    ... | no _ | Define path mult name₃ τ₂ val₂ = ((def mult name₂ τ₁ val₁ ∷_) ***′ (λ p → Define p mult name₃ τ₂ val₂)) (set-multiplicity types path)
    ... | no _ | Bind path mult name₃ τ₂ = ((def mult name₂ τ₁ val₁ ∷_) ***′ (λ p → Bind p mult name₃ τ₂)) (set-multiplicity types path)

-- | Lookup a multiplicity and type by name.
lookup : ∀ {n} → Located String → Context n → Maybe (Located Multiplicity × Located Value)
lookup name ctx = go name types
  where 
    open Context ctx

    go : ∀ {n} → Located String → Vec Binding n → Maybe (Located Multiplicity × Located Value)
    go _ [] = nothing
    go name@(n₁ at _) (def m (n₂ at _) _ τ ∷ ts) with n₁ == n₂
    ... | yes _ = just (m , τ)
    ... | no _ = go name ts

index-context : ∀ {n} → (m : Nat) → {{_ : IsTrue (lessNat m n)}} → Context n → (Located Multiplicity × Located String × Located Value)
index-context m ctx = 
  let def m n _ τ = indexVec types (natToFin m)
   in m , n , τ
  where open Context ctx

open Context hiding (is-lvl-consistent) public 