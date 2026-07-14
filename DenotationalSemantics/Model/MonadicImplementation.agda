------------------------------------------------------------------------
-- IMPLEMENTING THE OPERATIONS IN THE RUNTIME MONAD.                     --
--                                                                    --
-- The external implementation `op-semᵐ` of an operation returns its      --
-- arity value inside the runtime monad `Mᵒ`, so running an operation     --
-- performs an `Mᵒ`-effect as well as taking `op-grade op` worth of time. --
--                                                                    --
-- For the tick monad to absorb those effects, each `Tᵏ A ε` is an        --
-- `Mᵒ`-algebra (`algᴹ`). Running an operation is then: compute the arity --
-- value in `Mᵒ`, carry the environment into it with the strength, run    --
-- the continuation, and fold the resulting `Mᵒ (Tᵏ A ε)` with `algᴹ` —   --
-- leaving, as in the pure case, an `op-grade op`-tick.                   --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Data.Nat using (ℕ)

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.Monad
open import DenotationalSemantics.Model.TickMonad
open import DenotationalSemantics.Model.RuntimeMonad

module DenotationalSemantics.Model.MonadicImplementation
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
         (TMon : TickMonad S Cat Fut)
         (RMon : RuntimeMonad Cat)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon using (Tᵒ; Tᶠ; ηᵀ; μᵀ; T-≤; ε-substᵀ; delayᵀ; opᵀ)
open TickMonad TMon
open RuntimeMonad RMon

record MonadicImplementation : Set₁ where

  field

    -- THE TICK MONAD'S COMPUTATIONS ARE Mᵒ-ALGEBRAS
    --
    -- This is what makes the semantic monad's effects part of a top-level
    -- computation. It is the only interaction between the two monads.

    algᴹ : ∀ {A ε} → Mᵒ (Tᵏ A ε) →ᵐ Tᵏ A ε

    algᴹ-ηᴹ : ∀ {A ε} → algᴹ {A} {ε} ∘ᵐ ηᴹ ≈ᵐ idᵐ
    algᴹ-μᴹ : ∀ {A ε} → algᴹ {A} {ε} ∘ᵐ μᴹ ≈ᵐ algᴹ ∘ᵐ Mᶠ algᴹ

    algᴹ-nat : ∀ {A B ε} → (f : A →ᵐ B)
             → algᴹ {B} {ε} ∘ᵐ Mᶠ (Tᵏᶠ f) ≈ᵐ Tᵏᶠ f ∘ᵐ algᴹ

    -- The external implementation: from the parameter, as seen from
    -- `mapᵉ (op-grade op)` in its future, the arity value the operation
    -- returns — inside the semantic monad.

    op-semᵐ : (op : Op)
            → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ param op ⟧ᵍ →ᵐ Mᵒ ⟦ arity op ⟧ᵍ

    -- Running a computation's operations. A graded monad morphism …

    implᵐ : ∀ {A ε} → Tᵒ A ε →ᵐ Tᵏ A ε

    implᵐ-ηᵀ : ∀ {A} → implᵐ ∘ᵐ ηᵀ {A} ≈ᵐ ηᵏ
    implᵐ-μᵀ : ∀ {A ε ε'}
             → implᵐ ∘ᵐ μᵀ {A} {ε} {ε'}
             ≈ᵐ μᵏ ∘ᵐ Tᵏᶠ implᵐ ∘ᵐ implᵐ
    implᵐ-nat : ∀ {A B ε} → (f : A →ᵐ B)
              → implᵐ {ε = ε} ∘ᵐ Tᶠ f ≈ᵐ Tᵏᶠ f ∘ᵐ implᵐ
    implᵐ-T-≤ : ∀ {A ε ε'} → (p : ε ≾ₑ ε')
              → implᵐ {A} ∘ᵐ T-≤ p ≈ᵐ T-≤ᵏ p ∘ᵐ implᵐ
    implᵐ-ε-subst : ∀ {A ε ε'} → (e : ε ≡ ε')
                  → implᵐ {A} ∘ᵐ ε-substᵀ e ≈ᵐ ε-substᵏ e ∘ᵐ implᵐ

    -- … it keeps a delay a delay …

    implᵐ-delayᵀ : ∀ {A ε} → (τ : ℕ)
                 → implᵐ ∘ᵐ delayᵀ {A} {ε} τ
                 ≈ᵐ tickᵏ (of-natᵉ τ)
                    ∘ᵐ []-≤ (≾ᵣ-reflexive map-of-natᵉ)
                    ∘ᵐ [ of-natʳ τ ]ᶠ implᵐ

    -- … and it runs an operation away: the arity value is computed in `Mᵒ`,
    -- the environment is carried into it by the strength, and the `Mᵒ`-effects
    -- the continuation is then run under are absorbed by the algebra. Only the
    -- operation's tick is left.

    implᵐ-opᵀ : ∀ {X A ε} → (op : Op)
              → (v : X →ᵐ ⟦ param op ⟧ᵍ)
              → (k : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ A ε)
              → implᵐ ∘ᵐ (opᵀ op
                          ∘ᵐ ⟨ v , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ k) ∘ᵐ η⊣ ⟩ᵐ)
              ≈ᵐ tickᵏ (op-grade op)
                 ∘ᵐ [ mapᵉ (op-grade op) ]ᶠ
                      (algᴹ
                       ∘ᵐ Mᶠ (implᵐ ∘ᵐ k)
                       ∘ᵐ strᴹ
                       ∘ᵐ ⟨ idᵐ , op-semᵐ op ∘ᵐ ⟨ mapᵉ (op-grade op) ⟩ᶠ v ⟩ᵐ)
                 ∘ᵐ η⊣
