---------------------------------------
-- Well-typed syntax of the language --
---------------------------------------

open import Syntax.Grades

module Syntax.Language (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Nat public
open import Data.Product 

open import Syntax.Contexts (Grades)
open import Syntax.Extensions (Grades)
open import Syntax.Types (Grades)
open import Syntax.Renamings (Grades)

open import Util.Equality
open import Util.Operations (Grades)

-- Well-typed terms (values and computations)

infix 26 _⊢V⦂_
infix 26 _⊢C⦂_

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where

    -- variables

    var     : {A : VType}
            → A ∈[ uᵣ ] Γ
            ------------
            → Γ ⊢V⦂ A

    -- base-typed constants

    const   : {B : BaseType}
            → BaseSet B
            ----------------
            → Γ ⊢V⦂ Base B

    -- unit type

    ⋆       :
            ------------
              Γ ⊢V⦂ Unit

    -- pairing

    ⦉_,_⦊    : {A B : VType}
            → Γ ⊢V⦂ A
            → Γ ⊢V⦂ B
            ---------------
            → Γ ⊢V⦂ A |×| B

    -- lambda abstraction
          
    lam     : {A : VType}
            → {C : CType}
            → Γ ∷ A ⊢C⦂ C
            -------------
            → Γ ⊢V⦂ A ⇒ C


  data _⊢C⦂_ (Γ : Ctx) : CType → Set where

    -- returning a value

    return  : {A : VType}
            → Γ ⊢V⦂ A
            -------------
            → Γ ⊢C⦂ A ‼ uₑ

    -- sequential composition
    
    _;_     : {A B : VType}      -- NOTE: use \;0 to get this unicode semicolon
            → {ε' : E}
            → {ε : E}
            → Γ ⊢C⦂ A ‼ ε
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ------------------------
            → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')

    -- function application
    
    _·_     : {A : VType}
            → {C : CType}
            → Γ ⊢V⦂ A ⇒ C
            → Γ ⊢V⦂ A
            -------------
            → Γ ⊢C⦂ C

    -- pattern-matching

    match_`in_ : {A B : VType}
               → {C : CType}
               → Γ ⊢V⦂ A |×| B
               → Γ ∷ A ∷ B ⊢C⦂ C
               -----------------
               → Γ ⊢C⦂ C

    -- empty type elimination

    absurd  : {C : CType}
            → Γ ⊢V⦂ Empty
            -------------
            → Γ ⊢C⦂ C

    -- performing algebraic operations

    perform : {A : VType}
            → {ε : E}
            → (op : Op)
            → Γ ⊢V⦂ type-of-gtype (param op)
            → Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε
            ---------------------------------------------------------------
            → Γ ⊢C⦂ A ‼ ((op-grade op) ·ₑ ε)

    -- explicit delaying of a computation

    delay   : {A : VType}
            → (τ : ℕ)
            → {ε : E}
            → Γ ⟨ embedR τ ⟩ ⊢C⦂ A ‼ ε
            ------------------------------
            → Γ ⊢C⦂ A ‼ ((embedE τ) ·ₑ ε)

    -- effect handling

    handle_`with_`in
            : {A B : VType}
            → {ε ε' : E}
            → Γ ⊢C⦂ A ‼ ε
            → ((op : Op) → (ε'' : E) →
                 Γ ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                 ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ---------------------------------------------------------------------
            → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    unbox   : {A : VType}
            → {C : CType}
            → {Γ' : Ctx}
            → {ρ : R}
            → Ext Γ' Γ ρ
            → ctx-grade Γ ≾ᵣ ρ
            → Γ' ⊢V⦂ [ ρ ] A
            → Γ ∷ A ⊢C⦂ C
            ------------------
            → Γ ⊢C⦂ C

  {- Previous version:
    unbox   : {A : VType}
            → {C : CType}
            → {Γ₁ Γ₂ : Ctx}
            → {ρ : R} 
            → ctx-grade Γ₂ ≾ᵣ ρ 
            → Ren (Γ₁ ++ᶜ Γ₂) Γ
            → Γ₁ ⊢V⦂ [ ρ ] A
            → Γ ∷ A  ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C
  -}
    -- boxing up a value/resource that is ready for use in at least `ρ` grade steps

    box     : {A : VType}
            → {C : CType}
            → {ρ : R}
            → Γ ⟨ ρ ⟩ ⊢V⦂ A
            → Γ ∷ [ ρ ] A ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C

    -- sub-effecting

    -- coerce term

    coerce : {A : VType}
           → {ε ε' : E}
           → Γ ⊢C⦂ A ‼ ε
           → ε ≾ₑ ε'
           --------------
           → Γ ⊢C⦂ A ‼ ε'


-- Useful Substitution

ε-subst : ∀ {Γ A ε ε'}
          → ε ≡ ε'
          → Γ ⊢C⦂ A ‼ ε
          ---------------
          → Γ ⊢C⦂ A ‼ ε'

ε-subst refl M = M
