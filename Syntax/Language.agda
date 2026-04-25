---------------------------------------
-- Well-typed syntax of the language --
---------------------------------------

open import Syntax.Grades

module Syntax.Language (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Nat public
open import Data.Product
open import Data.Sum

open import Relation.Nullary using (¬_)

open import Syntax.Contexts (Grades)
open import Syntax.Types (Grades)

open import Util.Equality
open import Util.Operations (Grades)

-- Well-typed terms (values and computations)

infix 26 _⊢V⦂_
infix 26 _⊢C⦂_

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where

    -- variables

    var     : {A : VType}
            → {ρ : R}
            → (ρ ≾ᵣ uᵣ)
            → A ∈[ ρ ] Γ
            -------------
            → Γ ⊢V⦂ A

    -- base-typed constants

    const   : {B : BaseType}
            → BaseSet B
            ----------------
            → Γ ⊢V⦂ Base B

    -- unit type

    ⋆       :
              -----------
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
    
    _⍮_     : {A B : VType}      -- NOTE: use \;0 to get this unicode semicolon
            → {ε' : E}
            → {ε : E}
            → Γ ⊢C⦂ A ‼ ε
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            -----------------------------
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
            → {ε : E}
            → (τ : ℕ)
            → Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε
            ------------------------------
            → Γ ⊢C⦂ A ‼ (of-natᵉ τ ·ₑ ε)

    -- effect handling

    handle_`with_`in
            : {A B : VType}
            → {ε ε' : E}
            → Γ ⊢C⦂ A ‼ ε
            → ((op : Op) → (ε'' : E) → (Γ' : Ctx) →
                 (Γ ++ᶜ Γ') ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                 ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ---------------------------------------------------------------------
            → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    unbox   : {A : VType}
            → {C : CType}
            → {ρ ρ' : R}
            → (x : [ ρ ] A ∈[ ρ' ] Γ)
            → ρ' ≾ᵣ ρ
            → Γ ∷ A ⊢C⦂ C
            ---------------------------
            → Γ ⊢C⦂ C

    -- boxing up a value/resource that is ready for use in at least `ρ` grade steps

    box     : {A : VType}
            → {C : CType}
            → {ρ : R}
            → Γ ⟨ ρ ⟩ ⊢V⦂ A
            → Γ ∷ [ ρ ] A ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C

    -- (shallow explicit) sub-effecting

    coerce : {A : VType}
           → {ε ε' : E}
           → ε ≾ₑ ε'
           → Γ ⊢C⦂ A ‼ ε
           --------------
           → Γ ⊢C⦂ A ‼ ε'

-- Useful substitution of effect annotations

ε-subst : ∀ {Γ A ε ε'}
          → ε ≡ ε'
          → Γ ⊢C⦂ A ‼ ε
          ---------------
          → Γ ⊢C⦂ A ‼ ε'

ε-subst refl M = M

-- Values with graded modal types are variables

grad-typ⇒var : ∀ {Γ A ρ}
             → (V : Γ ⊢V⦂ [ ρ ] A)
             → Σ[ ρ' ∈ R ]
               Σ[ rel ∈ ρ' ≾ᵣ uᵣ ]
               Σ[ x ∈ ([ ρ ] A ∈[ ρ' ] Γ) ](V ≡ var rel x)
             
grad-typ⇒var (var rel x) = _ , rel , x , refl
