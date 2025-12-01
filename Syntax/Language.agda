---------------------------------------
-- Well-typed syntax of the language --
---------------------------------------

module Syntax.Language where

open import Syntax.Contexts
open import Syntax.Types

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Well-typed terms (values and computations)

infix 26 _⊢V⦂_
infix 26 _⊢C⦂_

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where

    -- variables

    var     : {A : VType}
            → {τ : Time}
            → A ∈[ τ ] Γ
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
            → Γ ⊢C⦂ A ‼ 0

    -- sequential composition
    
    _;_     : {A B : VType}      -- NOTE: use \;0 to get this unicode semicolon
            → {τ τ' : Time}
            → Γ ⊢C⦂ A ‼ τ
            → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
            ------------------------
            → Γ ⊢C⦂ B ‼ (τ + τ')
    
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
            → {τ : Time}
            → (op : Op)
            → Γ ⊢V⦂ type-of-gtype (param op)
            → Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ
            -------------------------------------------------------
            → Γ ⊢C⦂ A ‼ (op-time op + τ)

    -- explicit delaying of a computation

    delay   : {A : VType}
            → {τ' : Time}
            → (τ : Time)
            → Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ'
            --------------------
            → Γ ⊢C⦂ A ‼ (τ + τ')

    -- effect handling

    handle_`with_`in
            : {A B : VType}
            → {τ τ' : Time}
            → Γ ⊢C⦂ A ‼ τ
            → ((op : Op) → (τ'' : Time) →
                 Γ ∷ type-of-gtype (param op)
                   ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                 ⊢C⦂ B ‼ (op-time op + τ''))
            → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
            --------------------------------------------------
            → Γ ⊢C⦂ B ‼ (τ + τ')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    unbox   : {A : VType}
            → {C : CType}
            → {τ : Time}
            → τ ≤ ctx-time Γ
            → Γ -ᶜ τ ⊢V⦂ [ τ ] A
            → Γ ∷ A  ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C

    -- boxing up a value/resource that is ready for use in at least `τ` time steps

    box     : {A : VType}
            → {C : CType}
            → {τ : Time}
            → Γ ⟨ τ ⟩ ⊢V⦂ A
            → Γ ∷ [ τ ] A ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C


-- Usefull Substitution

τ-subst : ∀ {Γ A τ τ'}
        → τ ≡ τ'
        → Γ ⊢C⦂ A ‼ τ
        ---------------
        → Γ ⊢C⦂ A ‼ τ'

τ-subst refl M = M
