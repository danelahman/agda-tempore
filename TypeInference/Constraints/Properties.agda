------------------------------------------------------------------
-- Properties of constraint satisfaction                          --
--                                                                --
-- The two facts every consumer of the constraint language needs: --
--                                                                --
--   `⊨-mono`     — a solution survives any further substitution   --
--                  that also strengthens the residual hypotheses; --
--   `⊨-subst`/`⊨-subst⁻` — satisfying a substituted constraint is --
--                  satisfying the original along the composite.   --
--                                                                --
-- Both go by induction on the constraint, and both rest on        --
-- `⊨-resp-≐ˢ`: satisfaction only looks at a substitution          --
-- pointwise, so the binder cases may rearrange the substitutions  --
-- they build up to `_≐ˢ_`.                                        --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Constraints.Properties (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

≐ˢ-sym : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → σ' ≐ˢ σ
≐ˢ-sym p = mk≐ˢ (λ α → sym (≐ᵗ p α)) (λ i → sym (≐ʳ p i)) (λ i → sym (≐ᵉ p i))

≐ˢ-,ᵗ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (B : OVType Θ')
      → (σ ,ᵗ B) ≐ˢ (σ' ,ᵗ B)
≐ˢ-,ᵗ p B = mk≐ˢ (λ { zero → refl ; (suc α) → ≐ᵗ p α }) (≐ʳ p) (≐ᵉ p)

≐ˢ-,ʳ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (ρ : RExp Θ')
      → (σ ,ʳ ρ) ≐ˢ (σ' ,ʳ ρ)
≐ˢ-,ʳ p ρ = mk≐ˢ (≐ᵗ p) (λ { zero → refl ; (suc i) → ≐ʳ p i }) (≐ᵉ p)

≐ˢ-,ᵉ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (ε : EExp Θ')
      → (σ ,ᵉ ε) ≐ˢ (σ' ,ᵉ ε)
≐ˢ-,ᵉ p ε = mk≐ˢ (≐ᵗ p) (≐ʳ p) (λ { zero → refl ; (suc i) → ≐ᵉ p i })

≐ˢ-↑ᵉ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (σ ↑ᵉ) ≐ˢ (σ' ↑ᵉ)
≐ˢ-↑ᵉ p = mk≐ˢ (λ α → cong wkᵉ-v (≐ᵗ p α))
               (λ i → cong wkᵉ-r (≐ʳ p i))
               (λ { zero → refl ; (suc i) → cong wkᵉ-e (≐ᵉ p i) })

⊨-resp-≐ˢ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} {Q : Hyps Θ'}
          → σ ≐ˢ σ' → (C : Constraint Θ) → σ ⊨[ Q ] C → σ' ⊨[ Q ] C
⊨-resp-≐ˢ p ⊤̂                    s        = s
⊨-resp-≐ˢ p ⊥̂                    s        = s
⊨-resp-≐ˢ p (C ∧̂ D)              (s , t)  = ⊨-resp-≐ˢ p C s , ⊨-resp-≐ˢ p D t
⊨-resp-≐ˢ p (A ≐ᵥ B)             s        =
  trans (sym ([≐]ᵛ p A)) (trans s ([≐]ᵛ p B))
⊨-resp-≐ˢ {Q = Q} p (ρ ≾̂ᵣᶜ ρ')   s        =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') s
⊨-resp-≐ˢ {Q = Q} p (ε ≾̂ₑᶜ ε')   s        =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') s
⊨-resp-≐ˢ {Q = Q} p (Etᶜ A)      s        = subst (Q ⊩ᴱ_) ([≐]ᵛ p A) s
⊨-resp-≐ˢ {Q = Q} p (Et∨≾ᵘ A ρ)  (inj₁ s) = inj₁ (subst (Q ⊩ᴱ_) ([≐]ᵛ p A) s)
⊨-resp-≐ˢ {Q = Q} p (Et∨≾ᵘ A ρ)  (inj₂ s) =
  inj₂ (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([≐]ʳ p ρ) s)
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

  -- Composing two lifts lifts the composite

  ⨟-↑ᵉ : ∀ {Θ Θ' Θ''} → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → ((σ ↑ᵉ) ⨟ˢ (δ ↑ᵉ)) ≐ˢ ((σ ⨟ˢ δ) ↑ᵉ)
  ⨟-↑ᵉ σ δ = mk≐ˢ (λ α → wk-↑ᵉ-v δ (sTy σ α))
                  (λ i → wk-↑ᵉ-r δ (sR σ i))
                  (λ { zero → refl ; (suc i) → wk-↑ᵉ-e δ (sE σ i) })

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

  ↑ᵉ-,ᵉ : ∀ {Θ Θ₁ Θ'} → (δ : Subst Θ Θ₁) → (σ : Subst Θ₁ Θ') → (ε : EExp Θ')
        → ((δ ↑ᵉ) ⨟ˢ (σ ,ᵉ ε)) ≐ˢ ((δ ⨟ˢ σ) ,ᵉ ε)
  ↑ᵉ-,ᵉ δ σ ε = mk≐ˢ (λ α → wk-,ᵉ-v σ ε (sTy δ α))
                     (λ i → wk-,ᵉ-r σ ε (sR δ i))
                     (λ { zero → refl ; (suc i) → wk-,ᵉ-e σ ε (sE δ i) })

-- Transports hypothesis entailment along `_↑ᵉ`, for the `∀ᵉ` case of
-- `⊨-mono`; members of a weakened `Hyps` are read back with `∈-map⁻`.

⊩ᴴ-↑ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'}
      → Q' ⊩ᴴ Q [ δ ] → wkᵉ-H Q' ⊩ᴴ (wkᵉ-H Q) [ δ ↑ᵉ ]
⊩ᴴ-↑ᵉ {Θ} {Θ'} {Q} {Q'} {δ} h = mk⊩ᴴ ets↑ ordᵣ↑ ordₑ↑
  where
    ets↑ : ∀ {α} → α ∈ ets (wkᵉ-H Q) → wkᵉ-H Q' ⊩ᴱ sTy (δ ↑ᵉ) α
    ets↑ m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | α₀ , m₀ , refl = ⊩ᴱ-wkᵉ (⊩ets h m₀)

    ordᵣ↑ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
          → wkᵉ-H Q' ⊩ ρ [ δ ↑ᵉ ]ʳ ≾̂ᵣ ρ' [ δ ↑ᵉ ]ʳ
    ordᵣ↑ m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → wkᵉ-H Q' ⊩ x ≾̂ᵣ y)
             (sym (wk-↑ᵉ-r δ ρ₀)) (sym (wk-↑ᵉ-r δ ρ₀'))
             (⊩-wkᵉᵣ (⊩ordᵣ h m₀))

    ordₑ↑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
          → wkᵉ-H Q' ⊩ ε [ δ ↑ᵉ ]ᵉ ≾̂ₑ ε' [ δ ↑ᵉ ]ᵉ
    ordₑ↑ m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → wkᵉ-H Q' ⊩ x ≾̂ₑ y)
             (sym (wk-↑ᵉ-e δ ε₀)) (sym (wk-↑ᵉ-e δ ε₀'))
             (⊩-wkᵉₑ (⊩ordₑ h m₀))

⊨-mono : ∀ {Θ Θ' Θ''} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
           {δ : Subst Θ' Θ''} {Q' : Hyps Θ''}
       → Q' ⊩ᴴ Q [ δ ] → (C : Constraint Θ) → σ ⊨[ Q ] C → (σ ⨟ˢ δ) ⊨[ Q' ] C
⊨-mono h ⊤̂       s       = s
⊨-mono h ⊥̂       s       = s
⊨-mono h (C ∧̂ D) (s , t) = ⊨-mono h C s , ⊨-mono h D t
⊨-mono {σ = σ} {δ = δ} h (A ≐ᵥ B) s =
  trans (sym ([⨟]ᵛ A σ δ)) (trans (cong (_[ δ ]ᵛ) s) ([⨟]ᵛ B σ δ))
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (ρ ≾̂ᵣᶜ ρ') s =
  subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ) (⊩-substᵣ h s)
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (ε ≾̂ₑᶜ ε') s =
  subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ) (⊩-substₑ h s)
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (Etᶜ A) s =
  subst (Q' ⊩ᴱ_) ([⨟]ᵛ A σ δ) (⊩ᴱ-subst h s)
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (Et∨≾ᵘ A ρ) (inj₁ s) =
  inj₁ (subst (Q' ⊩ᴱ_) ([⨟]ᵛ A σ δ) (⊩ᴱ-subst h s))
⊨-mono {σ = σ} {δ = δ} {Q' = Q'} h (Et∨≾ᵘ A ρ) (inj₂ s) =
  inj₂ (subst (λ x → Q' ⊩ x ≾̂ᵣ ûᵣ) ([⨟]ʳ ρ σ δ) (⊩-substᵣ h s))
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
⊨-subst {δ = δ} {σ = σ} (A ≐ᵥ B) s =
  trans ([⨟]ᵛ A δ σ) (trans s (sym ([⨟]ᵛ B δ σ)))
⊨-subst {δ = δ} {σ = σ} {Q = Q} (ρ ≾̂ᵣᶜ ρ') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([⨟]ʳ ρ δ σ)) (sym ([⨟]ʳ ρ' δ σ)) s
⊨-subst {δ = δ} {σ = σ} {Q = Q} (ε ≾̂ₑᶜ ε') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([⨟]ᵉ ε δ σ)) (sym ([⨟]ᵉ ε' δ σ)) s
⊨-subst {δ = δ} {σ = σ} {Q = Q} (Etᶜ A) s =
  subst (Q ⊩ᴱ_) (sym ([⨟]ᵛ A δ σ)) s
⊨-subst {δ = δ} {σ = σ} {Q = Q} (Et∨≾ᵘ A ρ) (inj₁ s) =
  inj₁ (subst (Q ⊩ᴱ_) (sym ([⨟]ᵛ A δ σ)) s)
⊨-subst {δ = δ} {σ = σ} {Q = Q} (Et∨≾ᵘ A ρ) (inj₂ s) =
  inj₂ (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) (sym ([⨟]ʳ ρ δ σ)) s)
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
⊨-subst⁻ {δ = δ} {σ = σ} (A ≐ᵥ B) s =
  trans (sym ([⨟]ᵛ A δ σ)) (trans s ([⨟]ᵛ B δ σ))
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (ρ ≾̂ᵣᶜ ρ') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ δ σ) ([⨟]ʳ ρ' δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (ε ≾̂ₑᶜ ε') s =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε δ σ) ([⨟]ᵉ ε' δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (Etᶜ A) s =
  subst (Q ⊩ᴱ_) ([⨟]ᵛ A δ σ) s
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (Et∨≾ᵘ A ρ) (inj₁ s) =
  inj₁ (subst (Q ⊩ᴱ_) ([⨟]ᵛ A δ σ) s)
⊨-subst⁻ {δ = δ} {σ = σ} {Q = Q} (Et∨≾ᵘ A ρ) (inj₂ s) =
  inj₂ (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([⨟]ʳ ρ δ σ) s)
⊨-subst⁻ {δ = δ} {σ = σ} (∃ᵗ C) (B , s) =
  B , ⊨-resp-≐ˢ (↑ᵗ-,ᵗ δ σ B) C (⊨-subst⁻ C s)
⊨-subst⁻ {δ = δ} {σ = σ} (∃ʳ C) (ρ , s) =
  ρ , ⊨-resp-≐ˢ (↑ʳ-,ʳ δ σ ρ) C (⊨-subst⁻ C s)
⊨-subst⁻ {δ = δ} {σ = σ} (∃ᵉ C) (ε , s) =
  ε , ⊨-resp-≐ˢ (↑ᵉ-,ᵉ δ σ ε) C (⊨-subst⁻ C s)
⊨-subst⁻ {δ = δ} {σ = σ} (∀ᵉ C) s =
  ⊨-resp-≐ˢ (⨟-↑ᵉ δ σ) C (⊨-subst⁻ C s)
⊨-subst⁻ (⋀ᵒᵖ f) s = λ op → ⊨-subst⁻ (f op) (s op)

⊨-⊤ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} → σ ⊨[ Q ] ⊤̂
⊨-⊤ = tt

⊨-∧-intro : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {C D : Constraint Θ}
          → σ ⊨[ Q ] C → σ ⊨[ Q ] D → σ ⊨[ Q ] (C ∧̂ D)
⊨-∧-intro s t = s , t

⊨-∧-fst : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {C D : Constraint Θ}
        → σ ⊨[ Q ] (C ∧̂ D) → σ ⊨[ Q ] C
⊨-∧-fst (s , t) = s

⊨-∧-snd : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {C D : Constraint Θ}
        → σ ⊨[ Q ] (C ∧̂ D) → σ ⊨[ Q ] D
⊨-∧-snd (s , t) = t
