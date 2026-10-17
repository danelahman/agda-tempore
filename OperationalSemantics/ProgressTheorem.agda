open import Data.Empty

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.ProgressTheorem (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem S
open import OperationalSemantics.State               S

open import Syntax.Contexts S
open import Syntax.Language S
open import Syntax.Types    S

-- Progress theorem. A term is either returned value, operation or makes step

data Progresses : {ε : E}
                → {S : 𝕊 []}
                → {A : VType}
                → (M : toCtx S ⊢C⦂ A ‼ ε)
                →  Set where
                            
    is-value : {S : 𝕊 []}
             → {A : VType}
             → {V : toCtx S ⊢V⦂ A} 
               --------------------------
             → Progresses (return V) 

    is-op    : {ε : E}
             → {S : 𝕊 []}
             → {A : VType}
             → {op : Op}
             → {V : toCtx S ⊢V⦂ type-of-gtype (param op)}
             → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
               -------------------------------------------------------------------------
             → Progresses (perform op V M) 


    steps    : ∀ {ε'' ε'''}
             → {S S' : 𝕊 []} {A B : VType}
             → {M : toCtx S ⊢C⦂ A ‼ ε''}
             → {M' : toCtx S' ⊢C⦂  B ‼ ε''' }
             → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
             → (p : ≤ₛ-grade (step-extends-state M↝M') ·ᵣ mapᵉ ε''' ≾ᵣ mapᵉ ε'')
             → (t : B <:ᵛ A)
               --------------------------------------------------------------
             → Progresses M

-- Any reduction step witnesses progress: its two premises are `step-grade-≾`
-- and `step-refines-type`.

step-progress : ∀ {ε'' ε'''}
              → {S S' : 𝕊 []} {A B : VType}
              → {M : toCtx S ⊢C⦂ A ‼ ε''}
              → {M' : toCtx S' ⊢C⦂ B ‼ ε'''}
              → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                ---------------------------------
              → Progresses M
step-progress M↝M' = steps M↝M' (step-grade-≾ M↝M') (step-refines-type M↝M')

-- Progress theorem statement

progress : ∀ {A ε'} → {S : 𝕊 []} → (M : toCtx S ⊢C⦂ A ‼ ε') → Progresses M

progress (return V) = is-value
progress (M ⨟ N) with progress M
progress ((return V) ⨟ N) | is-value = step-progress SEQ-RET
... | is-op                          = step-progress SEQ-OP
progress (M ⨟ N) | steps M↝M' p _    = step-progress (SEQ-STEP M↝M' p)
progress (var ρ≾uᵣ x · W)          = ⊥-elim (⇒-not-in-toCtx x)
progress (lam M · W)               = step-progress APP
progress (subV V (_ ⇒ₛ (_ ‼ₛ _)) · W) = step-progress SUB-APP
progress (match P `in M)           = step-progress MATCH
progress (caseL V `nil M `cons N)  = step-progress CASEL
progress (recL V M N p)            = step-progress RECL
progress (absurd V)                = ⊥-elim (empty-not-value V)
progress (if var ρ≾uᵣ x `then M `else N) = ⊥-elim (Bool-not-in-toCtx x)
progress (if true       `then M `else N) = step-progress IF-TRUE
progress (if false      `then M `else N) = step-progress IF-FALSE
progress (if subV V Boolₛ `then M `else N) = step-progress SUB-IF
progress (caseℕ var ρ≾uᵣ x `zero M `succ N) = ⊥-elim (Nat-not-in-toCtx x)
progress (caseℕ zero `zero M `succ N)       = step-progress CASEℕ-ZERO
progress (caseℕ succ V `zero M `succ N)     = step-progress CASEℕ-SUCC
progress (caseℕ subV V Natₛ `zero M `succ N) = step-progress SUB-CASEℕ
progress (recℕ (var ρ≾uᵣ x) M N p)       = ⊥-elim (Nat-not-in-toCtx x)
progress (recℕ zero M N p)                = step-progress RECℕ-ZERO
progress (recℕ (succ V) M N p)            = step-progress RECℕ-SUCC
progress (recℕ (subV V Natₛ) M N p)       = step-progress SUB-RECℕ
progress (case+ var ρ≾uᵣ x `inl M `inr N) = ⊥-elim (|+|-not-in-toCtx x)
progress (case+ inl V `inl M `inr N)      = step-progress CASE-INL
progress (case+ inr V `inl M `inr N)      = step-progress CASE-INR
progress (case+ subV V (_ |+|ₛ _) `inl M `inr N) = step-progress SUB-CASE
progress (perform op V M)          = is-op
progress (delay τ M)               = step-progress DELAY
progress (handle M `with H `in N) with progress M
progress (handle (return V) `with H `in N) | is-value = step-progress HANDLE-RET
... | is-op                     = step-progress HANDLE-OP
... | steps M↝M' p _            = step-progress (HANDLE-STEP M↝M' p)
progress (unbox _ _ _ _) = step-progress UNBOX
progress (box _ _)       = step-progress BOX
progress (subC M (_ ‼ₛ _)) = step-progress SUB

-- Theorem: is-value is indeed final state (make no further steps)

finality-value : ∀ {A B τ₂}
                → {S : 𝕊 []}
                → {S₁ : 𝕊 []}
                → {V : toCtx S ⊢V⦂ A}
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₂}
                → {uₑ≾ε : uₑ ≾ₑ τ₂}
                → ⟨ S , return V ⟩ ↝ ⟨ S₁ , M₁ ⟩
                → ⊥
finality-value ()


-- Theorem: is-op is indeed final state (make no further steps)

finality-op : ∀ {A B op τ₂ τ₃}
                → {S S₁ : 𝕊 []}
                → {V : toCtx S ⊢V⦂ type-of-gtype (param op) }
                → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ₂}
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₃}
                → ⟨ S , perform op V M ⟩ ↝ ⟨ S₁ , M₁ ⟩
                → ⊥
finality-op ()
