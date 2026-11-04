------------------------------------------------------------------
-- The top-level reduction of configurations                    --
--                                                              --
-- `⟨ 𝕊 ∣ M ⟩⟶ᵗ[ e ]⟨ 𝕊' ∣ M' ⟩`: a step of the reduction, or   --
-- an operation call run by its top-level implementation, which --
-- adds a passage of the operation's grade. A step preserves    --
-- the typing of the configuration as a step of the reduction   --
-- does (`top-level-preservation`).                             --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _,_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.OperationalSemantics.TopLevel.Reduction (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades                  S
open import PolymorphicCalculus.Syntax.Types                   S
open import PolymorphicCalculus.Syntax.Contexts                S
open import PolymorphicCalculus.Hypotheses                     S
open import PolymorphicCalculus.Typing                         S
open import PolymorphicCalculus.Typing.Renaming                S using (∥_∥ᵛ; ∥_∥ᶜ)
open import PolymorphicCalculus.Typing.Substitution            S
open import PolymorphicCalculus.Typing.Inversion               S
open import PolymorphicCalculus.Typing.ScopeClosed             S
open import PolymorphicCalculus.Syntax.Run                     S
open import PolymorphicCalculus.OperationalSemantics.State     S
open import PolymorphicCalculus.OperationalSemantics.Reduction S
open import PolymorphicCalculus.OperationalSemantics.TopLevel  S
open import PolymorphicCalculus.OperationalSemantics.TypeSafety S

-- Top-level small-step operational semantics, using the pure semantics
-- of algebraic operations, with its preservation theorem.

module PureTopLevelPreservationTheorem (OpSemantics : TopLevelOpSemantics) where

  open TopLevelOpSemantics OpSemantics
  open Preserved

  data TopLevelStep {n} (𝕊 : State n) : RunC n → ∀ {m} (𝕊' : State m) → 𝕊 ≤ₛ 𝕊' → RunC m → Set

  infix 3 TopLevelStep
  syntax TopLevelStep 𝕊 M 𝕊' e M' = ⟨ 𝕊 ∣ M ⟩⟶ᵗ[ e ]⟨ 𝕊' ∣ M' ⟩

  data TopLevelStep {n} 𝕊 where

    -- Step according to the ordinary small-step semantics
    STEP    : ∀ {m} {𝕊' : State m} {e : 𝕊 ≤ₛ 𝕊'} {M M'}
            → ⟨ 𝕊 ∣ M ⟩⟶[ e ]⟨ 𝕊' ∣ M' ⟩
            → ⟨ 𝕊 ∣ M ⟩⟶ᵗ[ e ]⟨ 𝕊' ∣ M' ⟩

    -- Run a top-level implementation of an algebraic operation
    OP-STEP : ∀ {op V M}
            → ⟨ 𝕊 ∣ perform op V M ⟩⟶ᵗ[ ≤ₛ-⟨⟩ ≤ₛ-refl ]⟨ 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ₛ ∣
                M [ op-sem op 𝕊 V ]₀ ⟩

  -- A step, its extension of the state left implicit

  infix 3 ⟨_∣_⟩⟶ᵗ⟨_∣_⟩

  ⟨_∣_⟩⟶ᵗ⟨_∣_⟩ : ∀ {n m} → State n → RunC n → State m → RunC m → Set
  ⟨ 𝕊 ∣ M ⟩⟶ᵗ⟨ 𝕊' ∣ M' ⟩ = Σ[ e ∈ 𝕊 ≤ₛ _ ] ⟨ 𝕊 ∣ M ⟩⟶ᵗ[ e ]⟨ 𝕊' ∣ M' ⟩

  -- Reflexive-transitive closure: a run of the top-level machine.

  data TopLevelMultiStep {n} (𝕊 : State n) (M : RunC n) : ∀ {m} → State m → RunC m → Set

  infix 3 TopLevelMultiStep
  syntax TopLevelMultiStep 𝕊 M 𝕊' M' = ⟨ 𝕊 ∣ M ⟩⟶*ᵗ⟨ 𝕊' ∣ M' ⟩

  infixr 5 _▸_

  data TopLevelMultiStep {n} 𝕊 M where
    done : ⟨ 𝕊 ∣ M ⟩⟶*ᵗ⟨ 𝕊 ∣ M ⟩
    _▸_  : ∀ {k m} {𝕊₁ : State k} {e : 𝕊 ≤ₛ 𝕊₁} {M₁} {𝕊' : State m} {M'}
         → ⟨ 𝕊 ∣ M ⟩⟶ᵗ[ e ]⟨ 𝕊₁ ∣ M₁ ⟩ → ⟨ 𝕊₁ ∣ M₁ ⟩⟶*ᵗ⟨ 𝕊' ∣ M' ⟩
         → ⟨ 𝕊 ∣ M ⟩⟶*ᵗ⟨ 𝕊' ∣ M' ⟩

  -- Preservation for the top-level small-step operational semantics

  top-level-preservation : ∀ {n m} {𝕊 : State n} {𝕊' : State m} {e : 𝕊 ≤ₛ 𝕊'}
                             {Ψ : StateTyping 𝕊} {M M' X ε}
                         → Types Ψ → toCtx Ψ ⊢ᶜ M ⦂ X ! ε → ⟨ 𝕊 ∣ M ⟩⟶ᵗ[ e ]⟨ 𝕊' ∣ M' ⟩
                         → Preserved e Ψ M' X ε

  top-level-preservation T D (STEP s) = preservation T D s

  top-level-preservation {Ψ = Ψ} T (D , eD) (OP-STEP {op}) with invC≡ D eD
  ... | _ , (A , ε₁ , refl , (DV , eV) , (DM , eM)) , (p₀ !ₛ q₀)
      with op-sem-typed op T (DV , eV)
  ... | DW , eW = record
    { Ψ'      = Ψ ⟨⟩ˢ
    ; extends = ⊆-⟨⟩ ⊆-refl
    ; types   = T ⟨⟩ˢ
    ; X'      = A
    ; ε'      = ε₁
    ; typed   = sub-c (here (toCtx-defs Ψ)) DW DM ,
                trans (∥sub-c∥ (here (toCtx-defs Ψ)) DW DM) (cong₂ (subᶜ 0) eW eM)
    ; subtype = p₀
    ; grade   = transᵣ (monoᵣ (transᵣ (eqᵣ ≡̂ᵣ-identityˡ) gr) ⊩≾̂ᵣ-refl)
                       (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-map-·)) (map-mono q₀))
    }
    where
      gr : ∅ᴴ ⊩ rconst ∣ op-grade op ∣ᵉ ≾̂ᵣ ∣ econst (op-grade op) ∣̂ᵉ
      gr = eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-map-const)
