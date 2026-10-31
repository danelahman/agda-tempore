open import Data.Empty

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Progress (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           S
open import MonomorphicCalculus.OperationalSemantics.State               S

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Terms    S
open import MonomorphicCalculus.Syntax.Types    S

-- Progress: a term is a returned value or an operation, or it makes a step

data Progresses : {ε : E}
                → {𝕊 : State []}
                → {A : VType}
                → (M : toCtx 𝕊 ⊢C⦂ A ! ε)
                →  Set where
                            
    is-return  : {𝕊 : State []}
               → {A : VType}
               → {V : toCtx 𝕊 ⊢V⦂ A} 
                 --------------------------
               → Progresses (return V) 

    is-perform : {ε : E}
               → {𝕊 : State []}
               → {A : VType}
               → {op : Op}
               → {V : toCtx 𝕊 ⊢V⦂ ⌜ param op ⌝ᵍ}
               → {M : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε}
                 -------------------------------------------------------------------------
               → Progresses (perform op V M) 


    steps      : ∀ {ε'' ε'''}
               → {𝕊 𝕊' : State []} {A B : VType}
               → {M : toCtx 𝕊 ⊢C⦂ A ! ε''}
               → {M' : toCtx 𝕊' ⊢C⦂  B ! ε''' }
               → (M⟶M' : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
               → (p : κₛ (step-extends-state M⟶M') ·ᵣ ∣ ε''' ∣ᵉ ≾ᵣ ∣ ε'' ∣ᵉ)
               → (t : B <:ᵛ A)
                 --------------------------------------------------------------
               → Progresses M

-- Any reduction step witnesses progress: its two premises are `step-grade-≾`
-- and `step-refines-type`.

step-progress : ∀ {ε'' ε'''}
              → {𝕊 𝕊' : State []} {A B : VType}
              → {M : toCtx 𝕊 ⊢C⦂ A ! ε''}
              → {M' : toCtx 𝕊' ⊢C⦂ B ! ε'''}
              → (M⟶M' : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
                ---------------------------------
              → Progresses M
step-progress M⟶M' = steps M⟶M' (step-grade-≾ M⟶M') (step-refines-type M⟶M')

-- Progress theorem statement

progress : ∀ {A ε'} → {𝕊 : State []} → (M : toCtx 𝕊 ⊢C⦂ A ! ε') → Progresses M

progress (return V) = is-return
progress (M ⨟ N) with progress M
progress ((return V) ⨟ N) | is-return = step-progress SEQ-RET
... | is-perform                     = step-progress SEQ-OP
progress (M ⨟ N) | steps M⟶M' p _    = step-progress (SEQ-STEP M⟶M' p)
progress (var ρ≾𝟏ᵣ x · W)          = ⊥-elim (⇒-not-in-toCtx x)
progress (fun M · W)               = step-progress APP
progress (subV V (_ ⇒ₛ (_ !ₛ _)) · W) = step-progress SUB-APP
progress (match P `with M)         = step-progress MATCH
progress (matchL V `nil M `cons N) = step-progress MATCHL
progress (recL V M N p)            = step-progress RECL
progress (match+ V `inl M `inr N)  = step-progress MATCH+
progress (cmp ⋈ V W et)            = step-progress CMP
progress (absurd V)                = ⊥-elim (empty-not-value V)
progress (if var ρ≾𝟏ᵣ x `then M `else N) = ⊥-elim (bool-not-in-toCtx x)
progress (if true       `then M `else N) = step-progress IF-TRUE
progress (if false      `then M `else N) = step-progress IF-FALSE
progress (if subV V boolₛ `then M `else N) = step-progress SUB-IF
progress (matchℕ var ρ≾𝟏ᵣ x `zero M `succ N) = ⊥-elim (nat-not-in-toCtx x)
progress (matchℕ zero `zero M `succ N)       = step-progress MATCHℕ-ZERO
progress (matchℕ succ V `zero M `succ N)     = step-progress MATCHℕ-SUCC
progress (matchℕ subV V natₛ `zero M `succ N) = step-progress SUB-MATCHℕ
progress (recℕ (var ρ≾𝟏ᵣ x) M N p)       = ⊥-elim (nat-not-in-toCtx x)
progress (recℕ zero M N p)                = step-progress RECℕ-ZERO
progress (recℕ (succ V) M N p)            = step-progress RECℕ-SUCC
progress (recℕ (subV V natₛ) M N p)       = step-progress SUB-RECℕ
progress (perform op V M)          = is-perform
progress (delay τ M)               = step-progress DELAY
progress (handle M `with var _ x)  = ⊥-elim (⇛-not-in-toCtx x)
progress (handle M `with handler N H) with progress M
progress (handle (return V) `with handler N H) | is-return = step-progress HANDLE-RET
... | is-perform                = step-progress HANDLE-OP
... | steps M⟶M' p _            = step-progress (HANDLE-STEP M⟶M' p)
progress (handle M `with subV (var _ x) (_ ⇛ₛ _)) = ⊥-elim (⇛-not-in-toCtx x)
progress (handle M `with subV (handler N H) ((_ !ₛ _) ⇛ₛ _)) =
  step-progress SUB-HANDLE
progress (handle M `with subV (subV V p) p') = step-progress SUB-HANDLE-TRANS
progress (unbox _ _ _ _) = step-progress UNBOX
progress (box _ _ _)       = step-progress BOX
progress (subC M (_ !ₛ _)) = step-progress SUB

-- is-return is final: it makes no further steps

finality-value : ∀ {A B τ₂}
                → {𝕊 : State []}
                → {𝕊₁ : State []}
                → {V : toCtx 𝕊 ⊢V⦂ A}
                → {M₁ : toCtx 𝕊₁ ⊢C⦂ B ! τ₂}
                → {𝟏ₑ≾ε : 𝟏ₑ ≾ₑ τ₂}
                → ⟨ 𝕊 ∣ return V ⟩ ⟶ ⟨ 𝕊₁ ∣ M₁ ⟩
                → ⊥
finality-value ()


-- is-perform is final: it makes no further steps

finality-op : ∀ {A B op τ₂ τ₃}
                → {𝕊 𝕊₁ : State []}
                → {V : toCtx 𝕊 ⊢V⦂ ⌜ param op ⌝ᵍ }
                → {M : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! τ₂}
                → {M₁ : toCtx 𝕊₁ ⊢C⦂ B ! τ₃}
                → ⟨ 𝕊 ∣ perform op V M ⟩ ⟶ ⟨ 𝕊₁ ∣ M₁ ⟩
                → ⊥
finality-op ()
