module OperationalSemantics.TheoremsAboutSteps where


open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Types

open import OperationalSemantics.PreservationTheorem
open import OperationalSemantics.State

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
open import Syntax.Operations
open import Util.Time

open Eq.≡-Reasoning

-- Theorem that step only increases time

step-increases-time : ∀ {A τ'' τ'''} → 
                {S S' : 𝕊 []} 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ ) → 
                state-time S ≤ state-time S'
step-increases-time M↝M' = S≤ₛS'⇒τ≤τ' (step-extends-state M↝M')

-- step perserves overall time

conf-time+comp-time≡const : ∀ {A τ'' τ'''}
                → {S S' : 𝕊 []}
                → {M : toCtx S ⊢C⦂ A ‼ τ''}
                → {M' : toCtx S' ⊢C⦂ A ‼ τ'''}
                → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
                → (state-time S) + τ'' ≡ (state-time S') + τ'''
conf-time+comp-time≡const APP = refl
conf-time+comp-time≡const MATCH = refl
conf-time+comp-time≡const {S = S} {S' = S'} (SEQ-FST {τ₂ = τ₂} {τ₃} {τ₄} τ+τ₂≡τ₁+τ₄ M↝M') =
  begin 
      state-time S + (τ₂ + τ₃) ≡⟨ sym (+-assoc (state-time S) τ₂ τ₃) ⟩  
      state-time S + τ₂ + τ₃ ≡⟨ cong (_+ τ₃) τ+τ₂≡τ₁+τ₄ ⟩  
      state-time S' + τ₄ + τ₃ ≡⟨ +-assoc (state-time S') τ₄ τ₃ ⟩  
      state-time S' + (τ₄ + τ₃)
  ∎
conf-time+comp-time≡const SEQ-RET = refl
conf-time+comp-time≡const SEQ-OP = refl
conf-time+comp-time≡const {τ''' = τ'''} {S = S} (DELAY {τ' = τ'}) = 
    sym (+-assoc (state-time S) τ' τ''')
conf-time+comp-time≡const HANDLE-RET = refl
conf-time+comp-time≡const {S = S} {S' = S'} (HANDLE-STEP {τ₁ = τ₁} {τ₂ = τ₂} {τ₃} τ+τ₂≡τ₄+τ₃ M↝M') = 
  begin 
      state-time S + (τ₂ + τ₁) ≡⟨ sym (+-assoc (state-time S) τ₂ τ₁) ⟩  
      state-time S + τ₂ + τ₁ ≡⟨ cong (_+ τ₁) τ+τ₂≡τ₄+τ₃ ⟩  
      state-time S' + τ₃ + τ₁ ≡⟨ +-assoc (state-time S') τ₃ τ₁ ⟩  
      state-time S' + (τ₃ + τ₁)
  ∎
conf-time+comp-time≡const {S = S} (HANDLE-OP {τ' = τ'} {τ'' = τ''} {op = op}) = 
    cong ((state-time S) +_) (+-assoc (op-time op) τ'' τ')
conf-time+comp-time≡const BOX = refl
conf-time+comp-time≡const (UNBOX p) = refl
