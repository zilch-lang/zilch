module Language.Zilch.Typechecker.Elaborator.Class where

open import Language.Zilch.Typechecker.Metavars using (MetaContext)
open import Language.Zilch.Typechecker.Errors

open import Prelude.Nat using (Nat)
open import Prelude.List using (List)
open import Prelude.Function using (_$_; _∘_; id; flip)
open import Prelude.Product using (Exist; _×_; _,_)
open import Control.Monad.Writer public 
open import Control.Monad.State public 
open import Control.Monad.Except public
open import Control.Monad.Identity public
open import Control.Monad.Transformer public
open import Prelude.Monad public 
open import Prelude.Functor public 
open import Prelude.Applicative public
open import Prelude.Monoid using (MonoidList) public
open import Prelude.Sum using (left; Either)

open import Control.Monad.Extra public

Elaborator : Set → Set
Elaborator A = 
  WriterT (List ElabWarning) 
    (StateT (∃ N , MetaContext N) 
      (Except ElabError)) 
    A

runElaborator : ∀ {n A} → MetaContext n → Elaborator A → Either ElabError ((A × List ElabWarning) × (∃ n , MetaContext n))
runElaborator {n} ctx act = runExcept $ flip runStateT (n , ctx) $ runWriterT act

module _ {a} {E : Set a} {M : Set a → Set a} {A : Set a} where 
  -- why do I have to write this?
  throwError : {{_ : Monad M}} → E → ExceptT {a = a} E M A
  runExceptT (throwError err) = return (left err)

liftE : ∀ {A} → Except ElabError A → Elaborator A
liftE = lift ∘ lift
{-# INLINE liftE #-}

liftS : ∀ {A} → StateT (∃ N , MetaContext N) (Except ElabError) A → Elaborator A
liftS = lift 
{-# INLINE liftS #-}

liftW : ∀ {A} → WriterT (List ElabWarning) (StateT (∃ N , MetaContext N) (Except ElabError)) A → Elaborator A 
liftW = id 
{-# INLINE liftW #-}