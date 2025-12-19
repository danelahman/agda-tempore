---------------------------------------------------------------------------------
-- Well-typed syntax of the language and renamings actions on well-typed terms --
---------------------------------------------------------------------------------

open import Syntax.Grades

module Syntax.Language (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Contexts (Grades)
open import Syntax.Types (Grades)
open import Syntax.Renamings (Grades)

open import Util.Equality
open import Util.Operations (Grades)
open import Util.Time -- Remove

-- Well-typed terms (values and computations)

infix 26 _⊢V⦂_
infix 26 _⊢C⦂_

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where

    -- variables

    var     : {A : VType}
            → {ρ : R}
            → A ∈[ ρ ] Γ
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
            → Γ ⟨ mapᵉ (op-time op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε
            -------------------------------------------------------
            → Γ ⊢C⦂ A ‼ ((op-time op) ·ₑ ε)

    -- explicit delaying of a computation

    delay   : {A : VType}
            → (τ : ℕ)
            → {ε : E}
            → Γ ⟨ mapℕʳ τ ⟩ ⊢C⦂ A ‼ ε
            --------------------
            → Γ ⊢C⦂ A ‼ ((mapℕᵉ τ) ·ₑ ε)

    -- effect handling

    handle_`with_`in
            : {A B : VType}
            → {ε ε' : E}
            → Γ ⊢C⦂ A ‼ ε
            → ((op : Op) → (ε'' : E) →
                 Γ ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-time op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                 ⊢C⦂ B ‼ (op-time op ·ₑ ε''))
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            --------------------------------------------------
            → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    unbox   : {A : VType}
            → {C : CType}
            → {Γ₁ Γ₂ : Ctx}
            → {ρ : R}
            → ρ ≾ᵣ ctx-time Γ₂
            → Ren (Γ₁ ++ᶜ Γ₂) Γ 
            → Γ₁ ⊢V⦂ [ ρ ] A
            → Γ ∷ A  ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C

    -- boxing up a value/resource that is ready for use in at least `τ` time steps

    box     : {A : VType}
            → {C : CType}
            → {ρ : R}
            → Γ ⟨ ρ ⟩ ⊢V⦂ A
            → Γ ∷ [ ρ ] A ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C


-- Useful Substitution

ε-subst : ∀ {Γ A ε ε'}
        → ε ≡ ε'
        → Γ ⊢C⦂ A ‼ ε
        ---------------
        → Γ ⊢C⦂ A ‼ ε'

ε-subst refl M = M


-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename r (var x)    = var (proj₂ (proj₂ (var-rename r x)))
  V-rename r (const c)  = const c
  V-rename r ⋆          = ⋆
  V-rename r (⦉ V , W ⦊) = ⦉ V-rename r V , V-rename r W ⦊
  V-rename r (lam M)    = lam (C-rename (cong-ren r) M)

  C-rename : ∀ {Γ Γ' C}
           → Ren Γ Γ'
           → Γ ⊢C⦂ C
           ------------
           → Γ' ⊢C⦂ C

  C-rename r (return V)       = return (V-rename r V)
  C-rename r (M ; N)          = C-rename r M ; C-rename (cong-ren r) N
  C-rename r (V · W)          = V-rename r V · V-rename r W
  C-rename r (match V `in M)  = match V-rename r V `in C-rename (cong-ren r) M
  C-rename r (absurd V)       = absurd (V-rename r V)
  C-rename r (perform op V M) = perform op (V-rename r V) (C-rename (cong-ren r) M)
  C-rename r (delay τ M)      = delay τ (C-rename (cong-ren r) M)
  C-rename r (handle M `with H `in N) =
    handle C-rename r M
    `with (λ op τ'' → C-rename (cong-ren r) (H op τ'') )
    `in (C-rename (cong-ren r) N)
  C-rename r (unbox {A} {C} {Γ₁} {Γ₂} {ρ} rel r' V M) =
    unbox {A = A} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ρ = ρ}
      rel
      (r ∘ʳ r')
      (V-rename id-ren V)
      (C-rename (cong-ren r) M)

{-
      (≾ᵣ-trans ≾ᵣ-refl (≾ᵣ-trans rel (ctx-time-≾ r)))
      ({!!})
      (V-rename (ren ≾ᵣ-refl (λ {A = A₁} {ρ = ρ₁} z → ρ₁ , ≾ᵣ-refl , z)) V)
      (C-rename (cong-ren r) M)
-}
--    unbox (≾ᵣ-trans r (ctx-time-≾ r)) (V-rename (r -ʳ τ , p) V) (C-rename (cong-ren ρ) M)
  C-rename r (box V M)        = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)
