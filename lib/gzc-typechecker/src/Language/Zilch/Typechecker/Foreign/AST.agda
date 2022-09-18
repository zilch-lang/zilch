module Language.Zilch.Typechecker.Foreign.AST where

open import Data.Located using (Located)
open import Language.Zilch.Typechecker.Core.Multiplicity using (Multiplicity)

open import Prelude.String using (String)
open import Prelude.Bool using (Bool)
open import Prelude.Int using (Int)
open import Prelude.Maybe using (Maybe)
open import Prelude.List using (List)

{-# FOREIGN GHC import qualified Language.Zilch.Syntax.Core.AST as AST #-}

data HoleLoc : Set where
  SourceHole : HoleLoc 
  InsertedHole : HoleLoc
{-# COMPILE GHC HoleLoc = data AST.HoleLocation (AST.SourceHole | AST.InsertedHole) #-}

data IntegerSuffix : Set where
  SuffixU8 : IntegerSuffix
  SuffixU16 : IntegerSuffix 
  SuffixU32 : IntegerSuffix 
  SuffixU64 : IntegerSuffix 
  SuffixS8 : IntegerSuffix
  SuffixS16 : IntegerSuffix 
  SuffixS32 : IntegerSuffix 
  SuffixS64 : IntegerSuffix 
{-# COMPILE GHC IntegerSuffix = 
      data AST.IntegerSuffix 
        ( AST.SuffixU8 | AST.SuffixU16 | AST.SuffixU32 | AST.SuffixU64 
        | AST.SuffixS8 | AST.SuffixS16 | AST.SuffixS32 | AST.SuffixS64 
        )
#-}

mutual
  data Definition : Set where 
    D-let : Bool → Located Multiplicity → Located String → Located Expression → Located Expression → Definition 
    D-val : Located Multiplicity → Located String → Located Expression → Definition 
  {-# COMPILE GHC Definition = data AST.Definition (AST.Let | AST.Val) #-}

  data Parameter : Set where 
    Param : Bool → Located Multiplicity → Located String → Located Expression → Parameter
  {-# COMPILE GHC Parameter = data AST.Parameter (AST.Parameter) #-}

  data Expression : Set where 
    E-integer : Located String → IntegerSuffix → Expression
    E-character : Located String → Expression 
    E-identifier : Located String → Expression 
    E-λ_,_ : Located Parameter → Located Expression → Expression
    E-local : Located Definition → Located Expression → Expression
    E-app : Located Expression → Bool → Located Expression → Expression 
    E-type : Expression 
    E-hole : HoleLoc → Expression 
    E-Π_,_ : Located Parameter → Located Expression → Expression
    _E-⊗_ : Located Parameter → Located Expression → Expression 
    _E-&_ : Located Parameter → Located Expression → Expression
    _E-⊗,_ : Located Expression → Located Expression → Expression 
    _E-&,_ : Located Expression → Located Expression → Expression
    E-⊗unit : Expression
    E-&unit : Expression
    E-bool : Bool → Expression
    E-if_then_else_ : Located Expression → Located Expression → Located Expression → Expression
    E-one : Expression 
    E-⊤ : Expression
    E-fst : Located Expression → Expression 
    E-snd : Located Expression → Expression
    E-&access : Located Expression → Int → Expression
    E-⊗access : Located Expression → Located String → Expression
    E-⊗pair-elim : Maybe (Located String) → Located Multiplicity → Located String → Located String → Located Expression → Located Expression → Expression 
    E-⊗unit-elim : Maybe (Located String) → Located Multiplicity → Located Expression → Located Expression → Expression
  {-# COMPILE GHC Expression =
        data AST.Expression 
          ( AST.EInteger | AST.ECharacter | AST.EIdentifier | AST.ELam | AST.ELocal
          | AST.EApplication | AST.EType | AST.EHole | AST.EPi
          | AST.EMultiplicativeProduct | AST.EAdditiveProduct
          | AST.EMultiplicativePair | AST.EAdditivePair
          | AST.EMultiplicativeUnit | AST.EAdditiveUnit
          | AST.EBoolean | AST.EIfThenElse | AST.EOne | AST.ETop
          | AST.EFst | AST.ESnd | AST.EAdditiveTupleAccess | AST.EFieldAccess
          | AST.EMultiplicativePairElim | AST.EMultiplicativeUnitElim
          )
  #-}

data CallingConvention : Set where
  CCall : CallingConvention
{-# COMPILE GHC CallingConvention = data AST.CallingConvention (AST.CCall) #-}

data MetaAttribute : Set where
  Inline : MetaAttribute
  Foreign : Located CallingConvention → Located String → MetaAttribute
{-# COMPILE GHC MetaAttribute = data AST.MetaAttribute (AST.Inline | AST.Foreign) #-}

data TopLevel : Set where
  TopBind : Bool → List (Located MetaAttribute) → Located Definition → TopLevel
{-# COMPILE GHC TopLevel = data AST.TopLevel (AST.TopLevel) #-}

data Module : Set where 
  Mod : List (Located TopLevel) → Module 
{-# COMPILE GHC Module = data AST.Module (AST.Mod) #-}