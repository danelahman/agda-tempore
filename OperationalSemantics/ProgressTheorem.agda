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
             → {S S' : 𝕊 []} {A : VType}
             → {M : toCtx S ⊢C⦂ A ‼ ε''}
             → {M' : toCtx S' ⊢C⦂  A ‼ ε''' }
             → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
             → (p : ≤ₛ-grade (step-extends-state M↝M') ·ᵣ mapᵉ ε''' ≾ᵣ mapᵉ ε'')
               --------------------------------------------------------------
             → Progresses M

-- Progress theorem statement

progress : ∀ {A ε'} → {S : 𝕊 []} → (M : toCtx S ⊢C⦂ A ‼ ε') → Progresses M

progress (return V) = is-value
progress {ε' = ε'} {S = S} (M ⨟ N) with progress M
progress {S = S} (_⨟_ {ε' = ε'} (return V) N) | is-value =
  steps
    SEQ-RET
    (≾ᵣ-reflexive (sym (trans (map-·ᵉ {uₑ} {ε'}) (cong (_·ᵣ mapᵉ ε') map-uᵉ))))
... | is-op            = steps SEQ-OP (≾ᵣ-reflexive (·ᵣ-identityˡ _))
progress (_⨟_ {ε' = ε'} M N) | steps {ε''} {ε'''} {S = S} {S' = S'} M↝M' p =
  steps
    (SEQ-STEP M↝M' p)
    (≾ᵣ-trans
      (≾ᵣ-reflexive
        (trans (cong (≤ₛ-grade (step-extends-state M↝M') ·ᵣ_) (map-·ᵉ {ε'''} {ε'}))
               (sym (·ᵣ-assoc (≤ₛ-grade (step-extends-state M↝M')) (mapᵉ ε''') (mapᵉ ε')))))
      (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (≾ᵣ-reflexive (sym (map-·ᵉ {ε''} {ε'})))))
progress (var ρ≾uᵣ x · W)         = ⊥-elim (⇒-not-in-toCtx x)
progress (lam M · W)              = steps APP (≾ᵣ-reflexive (·ᵣ-identityˡ _))
progress (match var ρ≾uᵣ x `in M) = ⊥-elim (⦉⦊-not-in-toCtx x)
progress (match ⦉ V₁ , V₂ ⦊ `in M) = steps MATCH (≾ᵣ-reflexive (·ᵣ-identityˡ _))
progress (absurd (var ρ≾uᵣ x))    = ⊥-elim (Empty-not-in-toCtx x)
progress (perform op V M)         = is-op
progress {S = S} (delay {ε = ε} τ M) =
  steps
    DELAY
    (≾ᵣ-reflexive
      (trans
        (cong (_·ᵣ mapᵉ ε) (·ᵣ-identityˡ (of-natʳ _)))
        (trans
          (cong (_·ᵣ mapᵉ ε) (sym map-of-natᵉ))
          (sym map-·ᵉ))))
progress {S = S} (handle_`with_`in {ε' = ε'} M H N) with progress M
progress {S = S} (handle_`with_`in {ε' = ε'} (return V) H N) | is-value
  = steps
      HANDLE-RET
      (≾ᵣ-reflexive (sym (trans (map-·ᵉ {uₑ} {ε'}) (cong (_·ᵣ mapᵉ ε') map-uᵉ))))
... | is-op =
  steps
    HANDLE-OP
    (≾ᵣ-reflexive (trans (·ᵣ-identityˡ _) (cong (λ x → mapᵉ x) (sym (·ₑ-assoc (op-grade _) _ ε')))))
... | steps {ε'' = ε''} {ε''' = ε'''} {S' = S'} M↝M' p =
  steps
    (HANDLE-STEP M↝M' p)
    (≾ᵣ-trans
      (≾ᵣ-reflexive
        (trans (cong (≤ₛ-grade (step-extends-state M↝M') ·ᵣ_) (map-·ᵉ {ε'''} {ε'}))
               (sym (·ᵣ-assoc (≤ₛ-grade (step-extends-state M↝M')) (mapᵉ ε''') (mapᵉ ε')))))
      (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (≾ᵣ-reflexive (sym (map-·ᵉ {ε''} {ε'})))))
progress (unbox _ _ _)   = steps UNBOX (≾ᵣ-reflexive (·ᵣ-identityˡ _))
progress (box _ _)       = steps BOX (≾ᵣ-reflexive (·ᵣ-identityˡ _))
progress (coerce ε≾ε' _) = steps COERCE (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ _)) (map-monotoneᵉ ε≾ε'))

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
