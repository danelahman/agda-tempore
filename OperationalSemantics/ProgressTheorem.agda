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
             → {S S' : 𝕊 []} {A : VType}
             → {M : toCtx S ⊢C⦂ A ‼ ε''} 
             → {M' : toCtx S' ⊢C⦂  A ‼ ε''' }
             → (p : state-grade S' ·ᵣ mapᵉ ε''' ≾ᵣ state-grade S ·ᵣ mapᵉ ε'')
             → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
               --------------------------------------------------------------
             → Progresses M 

-- Progress theorem statement

progress : ∀ {A ε'} → {S : 𝕊 []} → (M : toCtx S ⊢C⦂ A ‼ ε') → Progresses M

progress (return V) = is-value
progress {ε' = ε'} {S = S} (M ; N) with progress M
progress {S = S} (_;_ {ε' = ε'} (return V) N) | is-value =
  steps
    (≾ᵣ-trans
      (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym (·ᵣ-identityˡ (mapᵉ ε')))))
      (≾ᵣ-trans
        (·ᵣ-monoʳ-≾ᵣ (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (sym uₑ≡ᵣuᵣ))))
        (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym (·-mapᵉ))))))
    SEQ-RET
... | is-op            = steps ≾ᵣ-refl SEQ-OP
progress (_;_ {ε' = ε'} M N) | steps {ε''} {ε'''} {S = S} {S' = S'} p M↝M' =
  steps
    (≾ᵣ-trans
      (≾ᵣ-trans
        (≾ᵣ-reflexive (trans (cong (state-grade S' ·ᵣ_) (·-mapᵉ {ε'''} {ε'})) (sym (·ᵣ-assoc _ _ _))))
        (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (≾ᵣ-reflexive (·ᵣ-assoc _ _ _))))
      (≾ᵣ-reflexive (sym (cong ((state-grade S) ·ᵣ_) (·-mapᵉ {ε''} {ε'})))))
    (SEQ-STEP p M↝M')
progress (var ρ≾uᵣ x · W)         = ⊥-elim (⇒-not-in-toCtx x)
progress (lam M · W)              = steps ≾ᵣ-refl APP
progress (match var ρ≾uᵣ x `in M) = ⊥-elim (⦉⦊-not-in-toCtx x)
progress (match ⦉ V₁ , V₂ ⦊ `in M) = steps ≾ᵣ-refl MATCH
progress (absurd (var ρ≾uᵣ x))    = ⊥-elim (Empty-not-in-toCtx x)
progress (perform op V M)         = is-op
progress {S = S} (delay {ε = ε} τ M) =
  steps
    (≾ᵣ-reflexive
      (trans
        (trans
          (cong (_·ᵣ mapᵉ ε) (cong (state-grade S ·ᵣ_) (sym (mapEmbedE≡embedR)))) (·ᵣ-assoc _ _ _))
        (cong (state-grade S ·ᵣ_) (sym ·-mapᵉ) )))
    DELAY
progress {S = S} (handle_`with_`in {ε' = ε'} M H N) with progress M
progress {S = S} (handle_`with_`in {ε' = ε'} (return V) H N) | is-value
  = steps
      ((≾ᵣ-trans
        (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym (·ᵣ-identityˡ (mapᵉ ε')))))
        (≾ᵣ-trans
          (·ᵣ-monoʳ-≾ᵣ (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (sym uₑ≡ᵣuᵣ))))
          (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym (·-mapᵉ)))))))
      HANDLE-RET
... | is-op =
  steps
    (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (cong (λ x → mapᵉ x) (sym (·ₑ-assoc (op-grade _) _ ε')))))
    HANDLE-OP
... | steps {ε'' = ε''} {ε''' = ε'''} {S' = S'} p M↝M' =
  steps
    ((≾ᵣ-trans
      (≾ᵣ-trans
        (≾ᵣ-reflexive (trans (cong (state-grade S' ·ᵣ_) (·-mapᵉ {ε'''} {ε'})) (sym (·ᵣ-assoc _ _ _))))
        (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (≾ᵣ-reflexive (·ᵣ-assoc _ _ _))))
      (≾ᵣ-reflexive (sym (cong ((state-grade S) ·ᵣ_) (·-mapᵉ {ε''} {ε'}))))))
    (HANDLE-STEP p M↝M')
progress (unbox _ _ _)   = steps ≾ᵣ-refl UNBOX
progress (box _ _)       = steps ≾ᵣ-refl BOX
progress (coerce ε≾ε' _) = steps (·ᵣ-monoʳ-≾ᵣ (pres-≾ᵉ ε≾ε')) COERCE

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
