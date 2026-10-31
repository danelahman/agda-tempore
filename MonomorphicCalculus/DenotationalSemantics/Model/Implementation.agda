-------------------------------------------------------------------------
-- Implementing the operations.                                        --
--                                                                     --
-- An external implementation `op-semᵐ` of each operation: from the    --
-- parameter, seen from `mapᵉ (op-grade op)` in its future (where the  --
-- continuation runs), the arity value. It is the semantic counterpart --
-- of `MonomorphicCalculus.OperationalSemantics.TopLevel.op-sem`, and  --
-- being a single morphism it is uniform in the state.                 --
--                                                                     --
-- Running the operations against it is a graded monad morphism from   --
-- the tree monad into the tick monad,                                 --
--                                                                     --
--   implᵐ : Tᵒ A ε →ᵐ Tᵏ A ε                                          --
--                                                                     --
-- which keeps leaves and delays, and replaces each operation node by  --
-- an `op-grade op`-tick, feeding its continuation the computed arity  --
-- value.                                                              --
-------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Data.Nat using (ℕ)

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad
open import MonomorphicCalculus.DenotationalSemantics.Model.TickMonad

module MonomorphicCalculus.DenotationalSemantics.Model.Implementation
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (TMon : TickMonad S Cat Fut)
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

record Implementation : Set₁ where

  field

    -- The external implementation: from the parameter, as seen from
    -- `mapᵉ (op-grade op)` in its future, the arity value the operation returns.

    op-semᵐ : (op : Op)
            → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ param op ⟧ᵍ →ᵐ ⟦ arity op ⟧ᵍ

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

    -- … it keeps a delay as a delay …

    implᵐ-delayᵀ : ∀ {A ε} → (τ : 𝔻)
                 → implᵐ ∘ᵐ delayᵀ {A} {ε} τ
                 ≈ᵐ tickᵏ (of-durᵉ τ)
                    ∘ᵐ []-≤ (≃ᵣ⇒≾ᵣ map-of-durᵉ)
                    ∘ᵐ [ of-durʳ τ ]ᶠ implᵐ

    -- … and it runs an operation away: the continuation is fed the computed
    -- arity value, and only the operation's tick is left.

    implᵐ-opᵀ : ∀ {X A ε} → (op : Op)
              → (v : X →ᵐ ⟦ param op ⟧ᵍ)
              → (k : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ A ε)
              → implᵐ ∘ᵐ (opᵀ op
                          ∘ᵐ ⟨ v , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ k) ∘ᵐ η⊣ ⟩ᵐ)
              ≈ᵐ tickᵏ (op-grade op)
                 ∘ᵐ [ mapᵉ (op-grade op) ]ᶠ
                     (implᵐ ∘ᵐ k
                      ∘ᵐ ⟨ idᵐ
                         , op-semᵐ op ∘ᵐ ⟨ mapᵉ (op-grade op) ⟩ᶠ v ⟩ᵐ)
                 ∘ᵐ η⊣
