------------------------------------------------------------------------
-- The TICK MONAD: the target of the pure top-level interpretation.      --
--                                                                    --
-- A graded monad with the same unit, multiplication, functorial action  --
-- and sub-effecting as `Monad`, but with no algebraic operations and no --
-- effect handling. In their place, a single primitive:                  --
--                                                                    --
--   tickᵏ δ : [ mapᵉ δ ]ᵒ (Tᵏ A ε) →ᵐ Tᵏ A (δ ·ₑ ε)                     --
--                                                                    --
-- a delay at an arbitrary effect grade: `δ` worth of time passes and     --
-- nothing is observed. A delay is `tickᵏ (of-durᵉ τ)`; an operation that --
-- has been implemented is `tickᵏ (op-grade op)`, leaving only the time   --
-- it took. `Model.Implementation` supplies the monad morphism running    --
-- the tree monad's operations into these ticks.                         --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future

module MonomorphicCalculus.DenotationalSemantics.Model.TickMonad
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open Category Cat
open Future Fut

record TickMonad : Set₁ where

  field

    -- THE GRADED MONAD

    Tᵏ : Obj → E → Obj
    Tᵏᶠ : ∀ {A B ε} → A →ᵐ B → Tᵏ A ε →ᵐ Tᵏ B ε

    ηᵏ : ∀ {A} → A →ᵐ Tᵏ A uₑ
    μᵏ : ∀ {A ε ε'} → Tᵏ (Tᵏ A ε') ε →ᵐ Tᵏ A (ε ·ₑ ε')

    -- transport along an equality of grades

    ε-substᵏ : ∀ {A ε ε'} → ε ≡ ε' → Tᵏ A ε →ᵐ Tᵏ A ε'
    ε-substᵏ-refl : ∀ {A ε} → ε-substᵏ {A} {ε} refl ≈ᵐ idᵐ

    -- sub-effecting

    T-≤ᵏ : ∀ {A ε₁ ε₂} → ε₁ ≾ₑ ε₂ → Tᵏ A ε₁ →ᵐ Tᵏ A ε₂

    -- Functoriality and congruence

    Tᵏ-idᵐ : ∀ {A ε} → Tᵏᶠ {A} {A} {ε} idᵐ ≈ᵐ idᵐ
    Tᵏ-∘ᵐ : ∀ {A B C ε} → (g : B →ᵐ C) → (f : A →ᵐ B)
          → Tᵏᶠ {A} {C} {ε} (g ∘ᵐ f) ≈ᵐ Tᵏᶠ g ∘ᵐ Tᵏᶠ f
    Tᵏ-congᶠ : ∀ {A B ε} {f g : A →ᵐ B} → f ≈ᵐ g → Tᵏᶠ {A} {B} {ε} f ≈ᵐ Tᵏᶠ g

    -- Unit and multiplication are natural

    ηᵏ-nat : ∀ {A B} → (f : A →ᵐ B) → ηᵏ ∘ᵐ f ≈ᵐ Tᵏᶠ f ∘ᵐ ηᵏ
    μᵏ-nat : ∀ {A B ε ε'} → (f : A →ᵐ B)
           → μᵏ {ε = ε} {ε' = ε'} ∘ᵐ Tᵏᶠ (Tᵏᶠ f) ≈ᵐ Tᵏᶠ f ∘ᵐ μᵏ

    -- Sub-effecting is natural and functorial in the grade

    T-≤ᵏ-nat : ∀ {A B ε ε'} → (f : A →ᵐ B) → (p : ε ≾ₑ ε')
             → Tᵏᶠ f ∘ᵐ T-≤ᵏ {A} p ≈ᵐ T-≤ᵏ {B} p ∘ᵐ Tᵏᶠ f
    T-≤ᵏ-refl : ∀ {A ε} → (p : ε ≾ₑ ε) → T-≤ᵏ {A} p ≈ᵐ idᵐ
    T-≤ᵏ-trans : ∀ {A ε₁ ε₂ ε₃} → (p : ε₁ ≾ₑ ε₂) → (q : ε₂ ≾ₑ ε₃) → (r : ε₁ ≾ₑ ε₃)
               → T-≤ᵏ {A} q ∘ᵐ T-≤ᵏ {A} p ≈ᵐ T-≤ᵏ {A} r
    T-≤ᵏ-≡ : ∀ {A ε ε'} → (e : ε ≡ ε')
           → ε-substᵏ {A} e ≈ᵐ T-≤ᵏ (≾ₑ-reflexive e)

    T-≤ᵏ-μᵏ : ∀ {A ε₁ ε₂ ε'} → (p : ε₁ ≾ₑ ε₂)
            → μᵏ {A} {ε₂} {ε'} ∘ᵐ T-≤ᵏ p
            ≈ᵐ T-≤ᵏ (·ₑ-monoˡ-≾ₑ p) ∘ᵐ μᵏ {A} {ε₁} {ε'}

    -- Graded monad laws

    Tᵏ-μ∘η≡id : ∀ {A ε}
              → μᵏ {A} {uₑ} {ε} ∘ᵐ ηᵏ {Tᵏ A ε}
              ≈ᵐ T-≤ᵏ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε))
    Tᵏ-μ∘Tη≡id : ∀ {A ε}
               → μᵏ {A} {ε} {uₑ} ∘ᵐ Tᵏᶠ (ηᵏ {A})
               ≈ᵐ T-≤ᵏ (≃ₑ⇒≿ₑ (·ₑ-identityʳ ε))
    Tᵏ-μ∘μ≡μ∘Tμ : ∀ {A ε ε' ε''}
                → μᵏ {A} {ε} {ε' ·ₑ ε''} ∘ᵐ Tᵏᶠ (μᵏ {A} {ε'} {ε''})
                ≈ᵐ T-≤ᵏ (≃ₑ⇒≾ₑ (·ₑ-assoc ε ε' ε'')) ∘ᵐ μᵏ ∘ᵐ μᵏ

    -- THE TICK
    --
    -- The only effect: `δ` worth of time passes, and nothing is observed.
    -- The computation resumes in the future the box reaches.

    tickᵏ : ∀ {A ε} → (δ : E) → [ mapᵉ δ ]ᵒ (Tᵏ A ε) →ᵐ Tᵏ A (δ ·ₑ ε)

    -- It is natural, algebraic, and sub-effecting passes under it: a tick
    -- records nothing, so coercing the continuation and coercing the whole
    -- computation agree.

    tickᵏ-nat : ∀ {A B ε} → (δ : E) → (f : A →ᵐ B)
              → tickᵏ {ε = ε} δ ∘ᵐ [ mapᵉ δ ]ᶠ (Tᵏᶠ f)
              ≈ᵐ Tᵏᶠ f ∘ᵐ tickᵏ δ

    tickᵏ-algebraicity : ∀ {A ε ε'} → (δ : E)
                       → μᵏ {A} {δ ·ₑ ε} {ε'} ∘ᵐ tickᵏ {ε = ε} δ
                       ≈ᵐ T-≤ᵏ (≃ₑ⇒≿ₑ (·ₑ-assoc δ ε ε'))
                         ∘ᵐ tickᵏ δ
                         ∘ᵐ [ mapᵉ δ ]ᶠ (μᵏ {A} {ε} {ε'})

    tickᵏ-≤ : ∀ {A ε ε'} → (δ : E) → (p : ε ≾ₑ ε')
            → tickᵏ {A} {ε'} δ ∘ᵐ [ mapᵉ δ ]ᶠ (T-≤ᵏ p)
            ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ p) ∘ᵐ tickᵏ {A} {ε} δ
