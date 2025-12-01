module OperationalSemantics.ProgressTheorem where


open import OperationalSemantics.PreservationTheorem
open import OperationalSemantics.State

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Types


open import Data.Empty
open import Util.Equality
open import Util.Operations
open import Util.Time

-- Progress theorem. A term is either returned value, operation or makes step

data Progresses : ∀ {τ'} → 
                {S : 𝕊 []} → 
                {A : VType} → 
                (M : toCtx S ⊢C⦂ A ‼ τ') →  Set where
                            
    is-value : {S : 𝕊 []} → 
            {A : VType} → 
            {V : toCtx S ⊢V⦂ A} →
            ---------------------
            Progresses (return V) 
    
    is-op : ∀ {τ'} → 
            {S : 𝕊 []} → 
            {A : VType} → 
            {op : Op} → 
            {V : toCtx S ⊢V⦂ type-of-gtype (param op) } → 
            {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ'} → 
            --------------------------------------------------------------------
            Progresses (perform op V M) 


    steps : ∀ {τ'' τ'''} → 
            {S S' : 𝕊 []} {A : VType} → 
            {M : toCtx S ⊢C⦂ A ‼ τ''} →
            {M' : toCtx S' ⊢C⦂  A ‼ τ''' } → 
            (p : state-time S + τ'' ≡ state-time S' + τ''') → 
            ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ →
            ----------------------------------
            Progresses M 

progress : ∀ {A τ'} → 
        {S : 𝕊 []} → 
        (M : toCtx S ⊢C⦂ A ‼ τ') → 
        Progresses M 
progress (return V) = is-value
progress {A = A} {τ' = τ'} {S = S} ((_;_) {τ' = τ₁} M N) with progress M
... | is-value = steps refl SEQ-RET 
... | is-op = steps refl (SEQ-OP {S = S})
... | steps {τ'' = τ₃} {τ''' = τ₄} {S' = S'} q M↝M' = 
    steps (step-time-eq (state-time S) τ₃ τ₁ (state-time S') τ₄ q) (SEQ-FST q M↝M')
progress (lam M · V) = steps refl APP
progress {S = S} (delay {τ' = τ₁} τ₂ M ) = 
    steps (sym (+-assoc (state-time S) τ₂ τ₁)) DELAY
progress (match ⦉ V , W ⦊ `in M) = steps refl MATCH
progress (perform op V M) = is-op
progress {S = S} (handle_`with_`in {τ' = τ₁} M H N) with progress M 
... | is-value = steps refl HANDLE-RET
... | is-op {τ' = τ'} {op = op} = 
        steps (τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ (state-time S) (op-time op) τ' τ₁) HANDLE-OP
... | steps {τ'' = τ₃} {τ''' = τ₄} {S' = S'} q M↝M' = 
    steps (step-time-eq (state-time S) τ₃ τ₁ (state-time S') τ₄ q) (HANDLE-STEP q M↝M')
progress (unbox τ≤ctx-time V M) = steps refl (UNBOX τ≤ctx-time)
progress (box V M) = steps refl BOX
progress (absurd (var V)) = ⊥-elim (Empty-not-in-toCtx V)
progress (var V · N) = ⊥-elim (⇒-not-in-toCtx V)
progress (match var V `in M) = ⊥-elim (⦉⦊-not-in-toCtx V)


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
                → {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ₂}
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₃}
                → ⟨ S , perform op V M ⟩ ↝ ⟨ S₁ , M₁ ⟩
                → ⊥
finality-op ()