------------------------------------------------------------------------
-- IMPLEMENTING THE OPERATIONS.                                          --
--                                                                    --
-- The pure top-level semantics runs every algebraic operation against an --
-- external implementation. Denotationally that is a graded monad         --
-- morphism from the tree monad into the tick monad,                      --
--                                                                    --
--   implᵐ : Tᵒ A ε →ᵐ Tᵏ A ε                                            --
--                                                                    --
-- which leaves leaves and delays alone and *runs away* every operation   --
-- node: it feeds the operation's continuation the arity value the        --
-- implementation computes, and what remains of the operation is the time --
-- it took — an `op-grade op`-tick.                                      --
--                                                                    --
-- The implementation itself is `op-semᵐ`: from the operation's parameter --
-- (seen from `mapᵉ (op-grade op)` in its future, which is where the      --
-- arity value is needed), the arity value. This is the semantic          --
-- counterpart of `OperationalSemantics.TopLevelOpSemantics.op-sem`, and  --
-- being a single morphism it is *automatically* uniform in the state —   --
-- which is the naturality condition `op-sem` is annotated as needing.    --
--                                                                    --
-- Note nothing here constrains `opᵀ`. The tree monad's operation node is --
-- what it is: a free node. What is assumed is only how it is *run*.      --
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

module DenotationalSemantics.Model.Implementation
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
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

    -- THE EXTERNAL IMPLEMENTATION OF THE OPERATIONS
    --
    -- Given the parameter — as seen from `mapᵉ (op-grade op)` in its future,
    -- which is where and when the operation's continuation runs — the arity
    -- value the operation returns.

    op-semᵐ : (op : Op)
            → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ param op ⟧ᵍ →ᵐ ⟦ arity op ⟧ᵍ

    -- RUNNING A COMPUTATION'S OPERATIONS

    implᵐ : ∀ {A ε} → Tᵒ A ε →ᵐ Tᵏ A ε

    -- It is a graded monad morphism …

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

    -- … and it RUNS AWAY an operation: the continuation is fed the arity
    -- value the implementation computes, and what is left of the operation is
    -- the time it took.

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
