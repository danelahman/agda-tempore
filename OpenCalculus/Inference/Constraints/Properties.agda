------------------------------------------------------------------
-- Properties of constraint satisfaction                        --
--                                                              --
--   * `⊨-mono`: a solution remains one along any further       --
--     substitution that also strengthens the residual          --
--     hypotheses.                                              --
--   * `⊨-subst`, `⊨-subst⁻`: a substituted constraint is       --
--     satisfied exactly when the original is satisfied along   --
--     the composite.                                           --
--   * `⊨-resp-≐ˢ`: satisfaction depends on a substitution only --
--     pointwise.                                               --
--   * `⊨-≐ᵥ`: types equal along a substitution solve a type    --
--     equation there.                                          --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Product using (_,_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.Constraints.Properties (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades S
open import OpenCalculus.Syntax.Types  S
open import OpenCalculus.Syntax.Subst  S
open import OpenCalculus.Hypotheses    S

open import OpenCalculus.Inference.Constraints.Syntax       S
open import OpenCalculus.Inference.Constraints.Satisfaction S

⊨-resp-≐ˢ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} {Q : Hyps Θ'}
          → σ ≐ˢ σ' → (C : Constraint Θ) → σ ⊨[ Q ] C → σ' ⊨[ Q ] C
⊨-resp-≐ˢ p ⊤̂                    s        = s
⊨-resp-≐ˢ p ⊥̂                    s        = s
⊨-resp-≐ˢ p (C ∧̂ D)              (s , t)  = ⊨-resp-≐ˢ p C s , ⊨-resp-≐ˢ p D t
⊨-resp-≐ˢ {Q = Q} p (A ≾̂ᵥᶜ B)    s        =
  subst₂ (Q ∣_<:̂ᵛ_) ([≐]ᵛ p A) ([≐]ᵛ p B) s
⊨-resp-≐ˢ {Q = Q} p (ρ ≾̂ᵣᶜ ρ')   s        =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') s
⊨-resp-≐ˢ {Q = Q} p (ε ≾̂ₑᶜ ε')   s        =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') s
⊨-resp-≐ˢ {Q = Q} p (Etᶜ A)      s        = subst (Q ⊩ᴱ_) ([≐]ᵛ p A) s
⊨-resp-≐ˢ {Q = Q} p (Et∨≾ᵘ A ρ)  s        =
  subst₂ (VarOK Q) ([≐]ᵛ p A) ([≐]ʳ p ρ) s
⊨-resp-≐ˢ p (∃ᵗ C)               (B , s)  = B , ⊨-resp-≐ˢ (≐ˢ-,ᵗ p B) C s
⊨-resp-≐ˢ p (∃ʳ C)               (ρ , s)  = ρ , ⊨-resp-≐ˢ (≐ˢ-,ʳ p ρ) C s
⊨-resp-≐ˢ p (∃ᵉ C)               (ε , s)  = ε , ⊨-resp-≐ˢ (≐ˢ-,ᵉ p ε) C s
⊨-resp-≐ˢ p (∀ᵉ C)               s        = ⊨-resp-≐ˢ (≐ˢ-↑ᵉ p) C s
⊨-resp-≐ˢ p (⋀ᵒᵖ f)              s        = λ op → ⊨-resp-≐ˢ p (f op) (s op)

private

  -- Composing an extension with a substitution extends the composite

  ⨟-,ᵗ : ∀ {Θ Θ' Θ''} → (σ : Subst Θ Θ') → (B : OVType Θ') → (δ : Subst Θ' Θ'')
       → ((σ ,ᵗ B) ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ) ,ᵗ (B [ δ ]ᵛ))
  ⨟-,ᵗ σ B δ = mk≐ˢ (λ { zero → refl ; (suc α) → refl }) (λ i → refl) (λ i → refl)

  ⨟-,ʳ : ∀ {Θ Θ' Θ''} → (σ : Subst Θ Θ') → (ρ : RExp Θ') → (δ : Subst Θ' Θ'')
       → ((σ ,ʳ ρ) ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ) ,ʳ (ρ [ δ ]ʳ))
  ⨟-,ʳ σ ρ δ = mk≐ˢ (λ α → refl) (λ { zero → refl ; (suc i) → refl }) (λ i → refl)

  ⨟-,ᵉ : ∀ {Θ Θ' Θ''} → (σ : Subst Θ Θ') → (ε : EExp Θ') → (δ : Subst Θ' Θ'')
       → ((σ ,ᵉ ε) ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ) ,ᵉ (ε [ δ ]ᵉ))
  ⨟-,ᵉ σ ε δ = mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

  -- A lift absorbs a following extension

  ↑ᵗ-,ᵗ : ∀ {Θ Θ₁ Θ'} → (δ : Subst Θ Θ₁) → (σ : Subst Θ₁ Θ') → (B : OVType Θ')
        → ((δ ↑ᵗ) ⨟ˢ (σ ,ᵗ B)) ≐ˢ ((δ ⨟ˢ σ) ,ᵗ B)
  ↑ᵗ-,ᵗ δ σ B = mk≐ˢ (λ { zero → refl ; (suc α) → wk-,ᵗ-v σ B (sTy δ α) })
                     (λ i → wk-,ᵗ-r σ B (sR δ i))
                     (λ i → wk-,ᵗ-e σ B (sE δ i))

  ↑ʳ-,ʳ : ∀ {Θ Θ₁ Θ'} → (δ : Subst Θ Θ₁) → (σ : Subst Θ₁ Θ') → (ρ : RExp Θ')
        → ((δ ↑ʳ) ⨟ˢ (σ ,ʳ ρ)) ≐ˢ ((δ ⨟ˢ σ) ,ʳ ρ)
  ↑ʳ-,ʳ δ σ ρ = mk≐ˢ (λ α → wk-,ʳ-v σ ρ (sTy δ α))
                     (λ { zero → refl ; (suc i) → wk-,ʳ-r σ ρ (sR δ i) })
                     (λ i → wk-,ʳ-e σ ρ (sE δ i))


⊨-mono : ∀ {Θ Θ' Θ''} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
           {δ : Subst Θ' Θ''} {Q' : Hyps Θ''}
       → Q' ⊩ᴴ Q [ δ ] → (C : Constraint Θ) → σ ⊨[ Q ] C → (σ ⨟ˢ δ) ⊨[ Q' ] C
⊨-mono h ⊤̂       s       = s
⊨-mono h ⊥̂       s       = s
⊨-mono h (C ∧̂ D) (s , t) = ⊨-mono h C s , ⊨-mono h D t
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (A ≾̂ᵥᶜ B) s =
  subst₂ (Q' ∣_<:̂ᵛ_) ([⨟]ᵛ A σ δ) ([⨟]ᵛ B σ δ) (<:̂ᵛ-subst h s)
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (ρ ≾̂ᵣᶜ ρ') s =
  subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ) (⊩-substᵣ h s)
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (ε ≾̂ₑᶜ ε') s =
  subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ) (⊩-substₑ h s)
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (Etᶜ A) s =
  subst (Q' ⊩ᴱ_) ([⨟]ᵛ A σ δ) (⊩ᴱ-subst h s)
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (Et∨≾ᵘ A ρ) s =
  subst₂ (VarOK Q') ([⨟]ᵛ A σ δ) ([⨟]ʳ ρ σ δ) (VarOK-subst h s)
⊨-mono {σ = σ} {δ = δ} h (∃ᵗ C) (B , s) =
  B [ δ ]ᵛ , ⊨-resp-≐ˢ (⨟-,ᵗ σ B δ) C (⊨-mono h C s)
⊨-mono {σ = σ} {δ = δ} h (∃ʳ C) (ρ , s) =
  ρ [ δ ]ʳ , ⊨-resp-≐ˢ (⨟-,ʳ σ ρ δ) C (⊨-mono h C s)
⊨-mono {σ = σ} {δ = δ} h (∃ᵉ C) (ε , s) =
  ε [ δ ]ᵉ , ⊨-resp-≐ˢ (⨟-,ᵉ σ ε δ) C (⊨-mono h C s)
⊨-mono {σ = σ} {δ = δ} h (∀ᵉ C) s =
  ⊨-resp-≐ˢ (⨟-↑ᵉ σ δ) C (⊨-mono (⊩ᴴ-↑ᵉ h) C s)
⊨-mono h (⋀ᵒᵖ f) s = λ op → ⊨-mono h (f op) (s op)

-- Both directions of satisfaction along a substitution.

⊨-subst : ∀ {Θ Θ₁ Θ'} {δ : Subst Θ Θ₁} {σ : Subst Θ₁ Θ'} {Q : Hyps Θ'}
        → (C : Constraint Θ) → (δ ⨟ˢ σ) ⊨[ Q ] C → σ ⊨[ Q ] C [ δ ]ᶜⁿ
⊨-subst ⊤̂       s       = s
⊨-subst ⊥̂       s       = s
⊨-subst (C ∧̂ D) (s , t) = ⊨-subst C s , ⊨-subst D t
⊨-subst {δ = δ} {σ = σ} {Q = Q} (A ≾̂ᵥᶜ B) s =
  subst₂ (Q ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A δ σ)) (sym ([⨟]ᵛ B δ σ)) s
⊨-subst {δ = δ} {σ = σ} {Q = Q} (ρ ≾̂ᵣᶜ ρ') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([⨟]ʳ ρ δ σ)) (sym ([⨟]ʳ ρ' δ σ)) s
⊨-subst {δ = δ} {σ = σ} {Q = Q} (ε ≾̂ₑᶜ ε') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([⨟]ᵉ ε δ σ)) (sym ([⨟]ᵉ ε' δ σ)) s
⊨-subst {δ = δ} {σ = σ} {Q = Q} (Etᶜ A) s =
  subst (Q ⊩ᴱ_) (sym ([⨟]ᵛ A δ σ)) s
⊨-subst {δ = δ} {σ = σ} {Q = Q} (Et∨≾ᵘ A ρ) s =
  subst₂ (VarOK Q) (sym ([⨟]ᵛ A δ σ)) (sym ([⨟]ʳ ρ δ σ)) s
⊨-subst {δ = δ} {σ = σ} (∃ᵗ C) (B , s) =
  B , ⊨-subst C (⊨-resp-≐ˢ (≐ˢ-sym (↑ᵗ-,ᵗ δ σ B)) C s)
⊨-subst {δ = δ} {σ = σ} (∃ʳ C) (ρ , s) =
  ρ , ⊨-subst C (⊨-resp-≐ˢ (≐ˢ-sym (↑ʳ-,ʳ δ σ ρ)) C s)
⊨-subst {δ = δ} {σ = σ} (∃ᵉ C) (ε , s) =
  ε , ⊨-subst C (⊨-resp-≐ˢ (≐ˢ-sym (↑ᵉ-,ᵉ δ σ ε)) C s)
⊨-subst {δ = δ} {σ = σ} (∀ᵉ C) s =
  ⊨-subst C (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ δ σ)) C s)
⊨-subst (⋀ᵒᵖ f) s = λ op → ⊨-subst (f op) (s op)

⊨-subst⁻ : ∀ {Θ Θ₁ Θ'} {δ : Subst Θ Θ₁} {σ : Subst Θ₁ Θ'} {Q : Hyps Θ'}
         → (C : Constraint Θ) → σ ⊨[ Q ] C [ δ ]ᶜⁿ → (δ ⨟ˢ σ) ⊨[ Q ] C
⊨-subst⁻ ⊤̂       s       = s
⊨-subst⁻ ⊥̂       s       = s
⊨-subst⁻ (C ∧̂ D) (s , t) = ⊨-subst⁻ C s , ⊨-subst⁻ D t
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (A ≾̂ᵥᶜ B) s =
  subst₂ (Q ∣_<:̂ᵛ_) ([⨟]ᵛ A δ σ) ([⨟]ᵛ B δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (ρ ≾̂ᵣᶜ ρ') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ δ σ) ([⨟]ʳ ρ' δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (ε ≾̂ₑᶜ ε') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε δ σ) ([⨟]ᵉ ε' δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (Etᶜ A) s =
  subst (Q ⊩ᴱ_) ([⨟]ᵛ A δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (Et∨≾ᵘ A ρ) s =
  subst₂ (VarOK Q) ([⨟]ᵛ A δ σ) ([⨟]ʳ ρ δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} (∃ᵗ C) (B , s) =
  B , ⊨-resp-≐ˢ (↑ᵗ-,ᵗ δ σ B) C (⊨-subst⁻ C s)
⊨-subst⁻ {δ = δ} {σ = σ} (∃ʳ C) (ρ , s) =
  ρ , ⊨-resp-≐ˢ (↑ʳ-,ʳ δ σ ρ) C (⊨-subst⁻ C s)
⊨-subst⁻ {δ = δ} {σ = σ} (∃ᵉ C) (ε , s) =
  ε , ⊨-resp-≐ˢ (↑ᵉ-,ᵉ δ σ ε) C (⊨-subst⁻ C s)
⊨-subst⁻ {δ = δ} {σ = σ} (∀ᵉ C) s =
  ⊨-resp-≐ˢ (⨟-↑ᵉ δ σ) C (⊨-subst⁻ C s)
⊨-subst⁻ (⋀ᵒᵖ f) s = λ op → ⊨-subst⁻ (f op) (s op)

-- A solution relative to hypotheses is one relative to them and any
-- obligations

⊨-∣ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {R : Obligs Θ'}
    → (C : Constraint Θ) → σ ⊨[ Q ] C → σ ⊨[ Q ∣ R ] C
⊨-∣ C s δ Q' (h , _) = ⊨-mono h C s

-- Types equal along a substitution solve a type equation

⊨-≐ᵥ : ∀ {Θ Θ'} {Q : Hyps Θ'} → (σ : Subst Θ Θ') → (A B : OVType Θ)
     → A [ σ ]ᵛ ≡ B [ σ ]ᵛ → σ ⊨[ Q ] (A ≐ᵥ B)
⊨-≐ᵥ {Q = Q} σ A B e =
  subst (Q ∣ A [ σ ]ᵛ <:̂ᵛ_) e (<:̂ᵛ-refl (A [ σ ]ᵛ)) ,
  subst (Q ∣_<:̂ᵛ A [ σ ]ᵛ) e (<:̂ᵛ-refl (A [ σ ]ᵛ))
