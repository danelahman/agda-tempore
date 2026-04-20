open import Syntax.Grades

module OperationalSemantics.ProgressTheorem (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import OperationalSemantics.PreservationTheorem (Grades)
open import OperationalSemantics.State (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Types (Grades)

open import Data.Empty
open import Util.Equality
open import Util.Operations (Grades)
open import Util.Time

-- Progress theorem. A term is either returned value, operation or makes step

data Progresses : {ε : E}
                → {S : 𝕊 []}
                → {A : VType}
                → (M : toCtx S ⊢C⦂ A ‼ ε)
                →  Set where
                            
    is-value : {ε : E}
             → {S : 𝕊 []}
             → {A : VType}
             → {uₑ≾ε : uₑ ≾ₑ ε}
             → {V : toCtx S ⊢V⦂ A} 
               --------------------------
             → Progresses (return uₑ≾ε V) 

    is-op    : {ε : E}
             → {S : 𝕊 []}
             → {A : VType}
             → {op : Op}
             → {V : toCtx S ⊢V⦂ type-of-gtype (param op)}
             → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
               -------------------------------------------------------------------------
             → Progresses (perform op V M) 


    steps    : ∀ {ε'' ε'''} 
             → {S S' : 𝕊 []} {A : VType}
             → {M : toCtx S ⊢C⦂ A ‼ ε''} 
             → {M' : toCtx S' ⊢C⦂  A ‼ ε''' }
             → (p : state-grade S ·ᵣ mapᵉ ε'' ≡ state-grade S' ·ᵣ mapᵉ ε''')
             → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
               --------------------------------------------------------------
             → Progresses M 

-- Progress theorem statement

progress : ∀ {A ε'} → {S : 𝕊 []} → (M : toCtx S ⊢C⦂ A ‼ ε') → Progresses M

progress (return uₑ≾ε V) = is-value
progress (M ; N) with progress M
... | is-value     = steps {!!} SEQ-RET
... | is-op        = steps refl SEQ-OP
... | steps p M↝M' = steps {!!} (SEQ-FST p M↝M')
progress (var ρ≾uᵣ x · W)         = ⊥-elim (⇒-not-in-toCtx x)
progress (lam M · W)              = steps refl APP
progress (match var ρ≾uᵣ x `in M) = ⊥-elim (⦉⦊-not-in-toCtx x)
progress (match ⦉ V₁ , V₂ ⦊ `in M) = steps refl MATCH
progress (absurd (var ρ≾uᵣ x))    = ⊥-elim (Empty-not-in-toCtx x)
progress (perform op V M)         = is-op
progress (delay τ M) =
  steps
    {!!}
    DELAY
progress (handle M `with H `in N) with progress M
... | is-value     = steps {!!} HANDLE-RET
... | is-op        = steps {!!} HANDLE-OP
... | steps p M↝M' = steps {!!} {!!}
progress (unbox x ρ'≾ρ M) = steps refl UNBOX
progress (box V M) = steps refl BOX
progress (coerce ε≾ε' M) with progress M
... | is-value     = steps refl COERCE-RET
... | is-op        = steps {!!} {!!}
... | steps p M↝M' = {!!}
{-
progress (return uₑ≾ε V) = is-value
progress {A = A} {τ' = τ'} {S = S} ((_;_) {ε' = ε₁} M N) with progress M
... | is-value = steps refl SEQ-RET 
... | is-op = steps refl (SEQ-OP {S = S})
... | steps {τ'' = τ₃} {τ''' = τ₄} {S' = S'} q M↝M' = 
    steps (step-time-eq (state-grade S) τ₃ ε₁ (state-grade S') τ₄ q) (SEQ-FST q M↝M')
progress (lam M · V) = steps refl APP
progress {S = S} (delay {τ' = τ₁} τ₂ M ) = 
    steps (sym (+-assoc (state-grade S) τ₂ τ₁)) DELAY
progress (match ⦉ V , W ⦊ `in M) = steps refl MATCH
progress (perform op V M) = is-op
progress {S = S} (handle_`with_`in {τ' = τ₁} M H N) with progress M 
... | is-value = steps refl HANDLE-RET
... | is-op {τ' = τ'} {op = op} = 
        steps (τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ (state-grade S) (op-grade op) τ' τ₁) HANDLE-OP
... | steps {τ'' = τ₃} {τ''' = τ₄} {S' = S'} q M↝M' = 
    steps (step-time-eq (state-grade S) τ₃ τ₁ (state-grade S') τ₄ q) (HANDLE-STEP q M↝M')
progress (unbox τ≤ctx-time V M) = steps refl (UNBOX τ≤ctx-time)
progress (box V M) = steps refl BOX
progress (absurd (var V)) = ⊥-elim (Empty-not-in-toCtx V)
progress (var V · N) = ⊥-elim (⇒-not-in-toCtx V)
progress (match var V `in M) = ⊥-elim (⦉⦊-not-in-toCtx V)
-}
{-
-- Theorem: is-value is indeed final state (make no further steps)

finality-value : ∀ {A B τ₂}
                → {S : 𝕊 []}
                → {S₁ : 𝕊 []}
                → {V : toCtx S ⊢V⦂ A}
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₂}
                → ⟨ S , return V ⟩ ↝ ⟨ S₁ , M₁ ⟩
                → ⊥
finality-value ()


-- Theorem: is-op is indeed final state (make no further steps)

finality-op : ∀ {A B op τ₂ τ₃}
                → {S S₁ : 𝕊 []}
                → {V : toCtx S ⊢V⦂ type-of-gtype (param op) }
                → {M : toCtx S ⟨ op-grade op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ₂}
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₃}
                → ⟨ S , perform op V M ⟩ ↝ ⟨ S₁ , M₁ ⟩
                → ⊥
finality-op ()
-}
