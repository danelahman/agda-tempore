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
open import OperationalSemantics.State                S

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
progress {ε' = ε'} {S = S} (M ⨟ N) with progress M
progress {S = S} (_⨟_ {ε' = ε'} (return V) N) | is-value =
  steps
    (≾ᵣ-trans
      (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym (·ᵣ-identityˡ (mapᵉ ε')))))
      (≾ᵣ-trans
        (·ᵣ-monoʳ-≾ᵣ (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (sym map-uᵉ))))
        (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym (map-·ᵉ))))))
    SEQ-RET
... | is-op            = steps ≾ᵣ-refl SEQ-OP
progress (_⨟_ {ε' = ε'} M N) | steps {ε''} {ε'''} {S = S} {S' = S'} p M↝M' =
  steps
    (≾ᵣ-trans
      (≾ᵣ-trans
        (≾ᵣ-reflexive (trans (cong (state-grade S' ·ᵣ_) (map-·ᵉ {ε'''} {ε'})) (sym (·ᵣ-assoc _ _ _))))
        (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (≾ᵣ-reflexive (·ᵣ-assoc _ _ _))))
      (≾ᵣ-reflexive (sym (cong ((state-grade S) ·ᵣ_) (map-·ᵉ {ε''} {ε'})))))
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
          (cong (_·ᵣ mapᵉ ε) (cong (state-grade S ·ᵣ_) (sym map-of-natᵉ))) (·ᵣ-assoc _ _ _))
        (cong (state-grade S ·ᵣ_) (sym map-·ᵉ) )))
    DELAY
progress {S = S} (handle_`with_`in {ε' = ε'} M H N) with progress M
progress {S = S} (handle_`with_`in {ε' = ε'} (return V) H N) | is-value
  = steps
      ((≾ᵣ-trans
        (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym (·ᵣ-identityˡ (mapᵉ ε')))))
        (≾ᵣ-trans
          (·ᵣ-monoʳ-≾ᵣ (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (sym map-uᵉ))))
          (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (sym map-·ᵉ))))))
      HANDLE-RET
... | is-op =
  steps
    (≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (cong (λ x → mapᵉ x) (sym (·ₑ-assoc (op-grade _) _ ε')))))
    HANDLE-OP
... | steps {ε'' = ε''} {ε''' = ε'''} {S' = S'} p M↝M' =
  steps
    ((≾ᵣ-trans
      (≾ᵣ-trans
        (≾ᵣ-reflexive (trans (cong (state-grade S' ·ᵣ_) (map-·ᵉ {ε'''} {ε'})) (sym (·ᵣ-assoc _ _ _))))
        (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (≾ᵣ-reflexive (·ᵣ-assoc _ _ _))))
      (≾ᵣ-reflexive (sym (cong ((state-grade S) ·ᵣ_) (map-·ᵉ {ε''} {ε'}))))))
    (HANDLE-STEP p M↝M')
progress (unbox _ _ _)   = steps ≾ᵣ-refl UNBOX
progress (box _ _)       = steps ≾ᵣ-refl BOX
progress (coerce ε≾ε' _) = steps (·ᵣ-monoʳ-≾ᵣ (map-monotoneᵉ ε≾ε')) COERCE

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
