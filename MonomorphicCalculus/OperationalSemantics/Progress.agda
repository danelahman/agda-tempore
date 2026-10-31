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
progress (case+ V `inl M `inr N)   = step-progress CASE+
progress (cmp ⋈ V W et)            = step-progress CMP
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
progress (perform op V M)          = is-op
progress (delay τ M)               = step-progress DELAY
progress (handle M `with var _ x)  = ⊥-elim (⇛-not-in-toCtx x)
progress (handle M `with handler N H) with progress M
progress (handle (return V) `with handler N H) | is-value = step-progress HANDLE-RET
... | is-op                     = step-progress HANDLE-OP
... | steps M↝M' p _            = step-progress (HANDLE-STEP M↝M' p)
progress (handle M `with subV (var _ x) (_ ⇛ₛ _)) = ⊥-elim (⇛-not-in-toCtx x)
progress (handle M `with subV (handler N H) ((_ ‼ₛ _) ⇛ₛ _)) =
  step-progress SUB-HANDLE
progress (handle M `with subV (subV V p) p') = step-progress SUB-HANDLE-TRANS
progress (unbox _ _ _ _) = step-progress UNBOX
progress (box _ _ _)       = step-progress BOX
progress (subC M (_ ‼ₛ _)) = step-progress SUB

-- is-value is final: it makes no further steps

finality-value : ∀ {A B τ₂}
                → {S : 𝕊 []}
                → {S₁ : 𝕊 []}
                → {V : toCtx S ⊢V⦂ A}
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₂}
                → {uₑ≾ε : uₑ ≾ₑ τ₂}
                → ⟨ S , return V ⟩ ↝ ⟨ S₁ , M₁ ⟩
                → ⊥
finality-value ()


-- is-op is final: it makes no further steps

finality-op : ∀ {A B op τ₂ τ₃}
                → {S S₁ : 𝕊 []}
                → {V : toCtx S ⊢V⦂ type-of-gtype (param op) }
                → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ₂}
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₃}
                → ⟨ S , perform op V M ⟩ ↝ ⟨ S₁ , M₁ ⟩
                → ⊥
finality-op ()
