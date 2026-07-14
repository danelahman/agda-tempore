------------------------------------------------------------------------
-- The TICK MONAD: the target of the top-level interpretation.           --
--                                                                    --
-- A graded monad on the same category, with the same unit,             --
-- multiplication, functorial action and sub-effecting as `Monad` — but   --
-- WITHOUT algebraic operations and without effect handling. In their     --
-- place it has a single primitive:                                      --
--                                                                    --
--   tickᵀ δ : [ mapᵉ δ ]ᵒ (Tᵒ A ε) →ᵐ Tᵒ A (δ ·ₑ ε)                     --
--                                                                    --
-- a *delay at an arbitrary effect grade*: trivial parameter, trivial     --
-- arity, and the grade as its effect. An ordinary delay is `tickᵀ        --
-- (of-natᵉ τ)`; an operation *that has been implemented* is `tickᵀ       --
-- (op-grade op)` — the operation's own passage of time, with nothing     --
-- left to observe.                                                     --
--                                                                    --
-- This is what the pure top-level semantics computes in. Its whole point --
-- is that every operation node of the tree monad gets run away by the    --
-- external implementations (`OperationalSemantics.TopLevelOpSemantics`), --
-- so what survives is only the time those operations took. The           --
-- `Implementation` structure (see `Model.Implementation`) is the graded  --
-- monad morphism that does the running.                                 --
--                                                                    --
-- Note this is NOT an instance of `Monad`: it deliberately lacks `opᵀ`   --
-- and `T-alg-of-handlerᵀ`, so the language's interpretation cannot be    --
-- re-instantiated at it (`⟦ perform … ⟧` and `⟦ handle … ⟧` need both).  --
-- Handling happens where it always did, in the tree monad; the           --
-- implementation applies to the operations that survive to the top.      --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future

module DenotationalSemantics.Model.TickMonad
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
              ≈ᵐ ε-substᵏ (sym (·ₑ-identityˡ ε))
    Tᵏ-μ∘Tη≡id : ∀ {A ε}
               → μᵏ {A} {ε} {uₑ} ∘ᵐ Tᵏᶠ (ηᵏ {A})
               ≈ᵐ ε-substᵏ (sym (·ₑ-identityʳ ε))
    Tᵏ-μ∘μ≡μ∘Tμ : ∀ {A ε ε' ε''}
                → μᵏ {A} {ε} {ε' ·ₑ ε''} ∘ᵐ Tᵏᶠ (μᵏ {A} {ε'} {ε''})
                ≈ᵐ ε-substᵏ (·ₑ-assoc ε ε' ε'') ∘ᵐ μᵏ ∘ᵐ μᵏ

    -- THE TICK
    --
    -- The only effect: `δ` worth of time passes, and nothing is observed.
    -- The computation resumes in the future the box reaches.

    tickᵏ : ∀ {A ε} → (δ : E) → [ mapᵉ δ ]ᵒ (Tᵏ A ε) →ᵐ Tᵏ A (δ ·ₑ ε)

    -- It is natural, algebraic, and sub-effecting passes under it.
    --
    -- The last is what the tree monad's `opᵀ` cannot satisfy: an operation
    -- node records the residual grade, so coercing the continuation and
    -- coercing the whole computation give different trees. A tick records
    -- nothing, so the two coincide — which is what lets a *run* of the
    -- top-level machine compose.

    tickᵏ-nat : ∀ {A B ε} → (δ : E) → (f : A →ᵐ B)
              → tickᵏ {ε = ε} δ ∘ᵐ [ mapᵉ δ ]ᶠ (Tᵏᶠ f)
              ≈ᵐ Tᵏᶠ f ∘ᵐ tickᵏ δ

    tickᵏ-algebraicity : ∀ {A ε ε'} → (δ : E)
                       → μᵏ {A} {δ ·ₑ ε} {ε'} ∘ᵐ tickᵏ {ε = ε} δ
                       ≈ᵐ ε-substᵏ (sym (·ₑ-assoc δ ε ε'))
                         ∘ᵐ tickᵏ δ
                         ∘ᵐ [ mapᵉ δ ]ᶠ (μᵏ {A} {ε} {ε'})

    tickᵏ-≤ : ∀ {A ε ε'} → (δ : E) → (p : ε ≾ₑ ε')
            → tickᵏ {A} {ε'} δ ∘ᵐ [ mapᵉ δ ]ᶠ (T-≤ᵏ p)
            ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ p) ∘ᵐ tickᵏ {A} {ε} δ
