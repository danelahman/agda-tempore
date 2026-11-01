------------------------------------------------------------------------
-- Type safety of the reduction                                       --
--                                                                    --
-- A configuration typed at `A ! ε` has finished or steps             --
-- (`progress`). A step extends the state (`step-extends-state`),     --
-- and the configuration it reaches is typed at `B ! ε'` with         --
-- `B <: A` and `κₛ e · ∣ ε' ∣ ≾ ∣ ε ∣` (`preservation`).             --
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations

module MonomorphicCalculus.OperationalSemantics.TypeSafety (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           S
open import MonomorphicCalculus.OperationalSemantics.State               S

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Terms    S
open import MonomorphicCalculus.Syntax.Types    S

------------------------------------------------------------------------
-- The statements

Steps : ∀ {A ε} → (𝕊 : State []) → toCtx 𝕊 ⊢ᶜ⦂ A ! ε → Set
Steps 𝕊 M =
  Σ[ B ∈ VType ] Σ[ ε' ∈ E ] Σ[ 𝕊' ∈ State [] ] Σ[ M' ∈ toCtx 𝕊' ⊢ᶜ⦂ B ! ε' ]
    ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩

-- What a step preserves. The state, the reached computation and its type
-- `B ! ε'` are those of the reached configuration, which is typed, so what
-- remains is how its type relates to the original `A ! ε`.

record Preserved {𝕊 𝕊' : State []} (e : 𝕊 ≤ₛ 𝕊') (B : VType) (ε' : E) (A : VType) (ε : E)
                 : Set where
  field
    subtype : B <:ᵛ A
    grade   : κₛ e ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ ∣ ε ∣ᵉ

open Preserved

------------------------------------------------------------------------
-- Preservation

preservation : ∀ {A B ε ε'} {𝕊 𝕊' : State []}
             → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε'}
             → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
             → Preserved (step-extends-state r) B ε' A ε
preservation r = record { subtype = step-refines-type r ; grade = step-grade-≾ r }

------------------------------------------------------------------------
-- Progress

private

  step : ∀ {A B ε ε'} {𝕊 𝕊' : State []}
       → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε'}
       → ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩ → Final M ⊎ Steps 𝕊 M
  step r = inj₂ (_ , _ , _ , _ , r)

progress : ∀ {A ε} {𝕊 : State []} → (M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε) → Final M ⊎ Steps 𝕊 M

progress (return V)       = inj₁ (is-return V)
progress (perform op V M) = inj₁ (is-perform op V M)

progress (M ⨟ N) with progress M
... | inj₁ (is-return V)        = step SEQ-RET
... | inj₁ (is-perform op V M') = step SEQ-OP
... | inj₂ (_ , _ , _ , _ , r)  = step (SEQ-STEP r (grade (preservation r)))

progress (var x ρ≾𝟏ᵣ · W)             = ⊥-elim (⇒-not-in-toCtx x)
progress (fun M · W)                  = step APP
progress (subV V (_ ⇒ₛ (_ !ₛ _)) · W) = step SUB-APP

progress (match P `with M)         = step MATCH
progress (matchL V `nil M `cons N) = step MATCHL
progress (recL V M N p)            = step RECL
progress (match+ V `inl M `inr N)  = step MATCH+
progress (absurd V)                = ⊥-elim (empty-not-value V)

progress (if var x ρ≾𝟏ᵣ `then M `else N)   = ⊥-elim (bool-not-in-toCtx x)
progress (if true `then M `else N)         = step IF-TRUE
progress (if false `then M `else N)        = step IF-FALSE
progress (if cmp ⋈ V W et `then M `else N) = step CMP
progress (if subV V boolₛ `then M `else N) = step SUB-IF

progress (matchℕ var x ρ≾𝟏ᵣ `zero M `succ N)  = ⊥-elim (nat-not-in-toCtx x)
progress (matchℕ zero `zero M `succ N)        = step MATCHℕ-ZERO
progress (matchℕ succ V `zero M `succ N)      = step MATCHℕ-SUCC
progress (matchℕ subV V natₛ `zero M `succ N) = step SUB-MATCHℕ

progress (recℕ (var x ρ≾𝟏ᵣ) M N p)  = ⊥-elim (nat-not-in-toCtx x)
progress (recℕ zero M N p)          = step RECℕ-ZERO
progress (recℕ (succ V) M N p)      = step RECℕ-SUCC
progress (recℕ (subV V natₛ) M N p) = step SUB-RECℕ

progress (delay τ M) = step DELAY

progress (handle M `with var x _)     = ⊥-elim (⇛-not-in-toCtx x)
progress (handle M `with handler N H) with progress M
... | inj₁ (is-return V)        = step HANDLE-RET
... | inj₁ (is-perform op V M') = step HANDLE-OP
... | inj₂ (_ , _ , _ , _ , r)  = step (HANDLE-STEP r (grade (preservation r)))
progress (handle M `with subV (var x _) (_ ⇛ₛ _))             = ⊥-elim (⇛-not-in-toCtx x)
progress (handle M `with subV (handler N H) ((_ !ₛ _) ⇛ₛ _)) = step SUB-HANDLE
progress (handle M `with subV (subV V p) p')                  = step SUB-HANDLE-TRANS

progress (unbox _ _ _ _)   = step UNBOX
progress (box _ _ _)       = step BOX
progress (subC M (_ !ₛ _)) = step SUB

------------------------------------------------------------------------
-- Type safety

type-safety : ∀ {A ε} {𝕊 : State []} → (M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε)
            → Final M
              ⊎ Σ[ B ∈ VType ] Σ[ ε' ∈ E ] Σ[ 𝕊' ∈ State [] ] Σ[ M' ∈ toCtx 𝕊' ⊢ᶜ⦂ B ! ε' ]
                  Σ[ r ∈ ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩ ] Preserved (step-extends-state r) B ε' A ε
type-safety M with progress M
... | inj₁ f                   = inj₁ f
... | inj₂ (_ , _ , _ , _ , r) = inj₂ (_ , _ , _ , _ , r , preservation r)
