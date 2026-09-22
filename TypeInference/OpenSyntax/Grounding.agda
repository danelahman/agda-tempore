------------------------------------------------------------------
-- Grounding the mirrored (open) language                         --
--                                                                --
-- A `Grounding Θ` assigns a closed type or grade to every        --
-- variable of the scope `Θ`, and the interpretations `⟦_⟧` send  --
-- every open expression, type and context to a closed one.       --
--                                                                --
-- On top of that sit the lemmas the grounding theorem consumes:  --
-- `θ ⊨ᴴ Q` (the grounding satisfies the hypothesis set),         --
-- groundings of convertibility, entailment, eternality,          --
-- subtyping and membership, the round-trips of the closed        --
-- embeddings, and the collapse of an effect-scope weakening.     --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Grounding (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts  S
open import Syntax.Types     S
open import Syntax.Subtyping S

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Hyps      S

record Grounding (Θ : Scope) : Set where
  constructor grounding
  field
    gTy : TyVar Θ → VType                  -- type variables to closed value types
    gR  : RVar Θ → R                       -- resource-grade variables to grades
    gE  : EVar Θ → E                       -- effect-grade variables to grades

open Grounding public

-- Extending a grounding along a scope extension. Defined by case analysis on
-- the variable rather than by composing with an injection, so that the
-- extension reduces on `zero` and on `suc`.

infixl 28 _,ᵍᵗ_ _,ᵍʳ_ _,ᵍᵉ_

_,ᵍᵗ_ : ∀ {Θ} → Grounding Θ → VType → Grounding (Θ +ty)
gTy (θ ,ᵍᵗ A) zero    = A
gTy (θ ,ᵍᵗ A) (suc α) = gTy θ α
gR  (θ ,ᵍᵗ A) i       = gR θ i
gE  (θ ,ᵍᵗ A) i       = gE θ i

_,ᵍʳ_ : ∀ {Θ} → Grounding Θ → R → Grounding (Θ +r)
gTy (θ ,ᵍʳ ρ) α       = gTy θ α
gR  (θ ,ᵍʳ ρ) zero    = ρ
gR  (θ ,ᵍʳ ρ) (suc i) = gR θ i
gE  (θ ,ᵍʳ ρ) i       = gE θ i

_,ᵍᵉ_ : ∀ {Θ} → Grounding Θ → E → Grounding (Θ +e)
gTy (θ ,ᵍᵉ ε) α       = gTy θ α
gR  (θ ,ᵍᵉ ε) i       = gR θ i
gE  (θ ,ᵍᵉ ε) zero    = ε
gE  (θ ,ᵍᵉ ε) (suc i) = gE θ i

-- Grade expressions: every former is sent to its closed counterpart, so in
-- particular `⟦ ûᵣ ⟧ʳ θ` is `uᵣ` and `⟦ ∣ ε ∣̂ᵉ ⟧ʳ θ` is `mapᵉ ⟦ ε ⟧ᵉ θ`.

⟦_⟧ᵉ : ∀ {Θ} → EExp Θ → Grounding Θ → E
⟦ evar i   ⟧ᵉ θ = gE θ i
⟦ econst ε ⟧ᵉ θ = ε
⟦ ε ·̂ₑ ε'  ⟧ᵉ θ = ⟦ ε ⟧ᵉ θ ·ₑ ⟦ ε' ⟧ᵉ θ
⟦ ε ⊔̂ₑ ε'  ⟧ᵉ θ = ⟦ ε ⟧ᵉ θ ⊔ₑ ⟦ ε' ⟧ᵉ θ

⟦_⟧ʳ : ∀ {Θ} → RExp Θ → Grounding Θ → R
⟦ rvar i   ⟧ʳ θ = gR θ i
⟦ rconst ρ ⟧ʳ θ = ρ
⟦ ρ ·̂ᵣ ρ'  ⟧ʳ θ = ⟦ ρ ⟧ʳ θ ·ᵣ ⟦ ρ' ⟧ʳ θ
⟦ ρ ⊔̂ᵣ ρ'  ⟧ʳ θ = ⟦ ρ ⟧ʳ θ ⊔ᵣ ⟦ ρ' ⟧ʳ θ
⟦ ∣ ε ∣̂ᵉ   ⟧ʳ θ = mapᵉ (⟦ ε ⟧ᵉ θ)

-- Types

mutual

  ⟦_⟧ᵛ : ∀ {Θ} → OVType Θ → Grounding Θ → VType
  ⟦ tvar α   ⟧ᵛ θ = gTy θ α
  ⟦ Base b   ⟧ᵛ θ = Base b
  ⟦ Unit     ⟧ᵛ θ = Unit
  ⟦ Bool     ⟧ᵛ θ = Bool
  ⟦ A |×| B  ⟧ᵛ θ = ⟦ A ⟧ᵛ θ |×| ⟦ B ⟧ᵛ θ
  ⟦ Empty    ⟧ᵛ θ = Empty
  ⟦ A ⇒ C    ⟧ᵛ θ = ⟦ A ⟧ᵛ θ ⇒ ⟦ C ⟧ᶜ θ
  ⟦ [ ρ ] A  ⟧ᵛ θ = [ ⟦ ρ ⟧ʳ θ ] ⟦ A ⟧ᵛ θ

  ⟦_⟧ᶜ : ∀ {Θ} → OCType Θ → Grounding Θ → CType
  ⟦ A ‼ ε ⟧ᶜ θ = ⟦ A ⟧ᵛ θ ‼ ⟦ ε ⟧ᵉ θ

-- Contexts

⟦_⟧ᶜᵗˣ : ∀ {Θ n} → OCtx Θ n → Grounding Θ → Ctx
⟦ []      ⟧ᶜᵗˣ θ = []
⟦ Γ ∷ A   ⟧ᶜᵗˣ θ = ⟦ Γ ⟧ᶜᵗˣ θ ∷ ⟦ A ⟧ᵛ θ
⟦ Γ ⟨ ρ ⟩ ⟧ᶜᵗˣ θ = ⟦ Γ ⟧ᶜᵗˣ θ ⟨ ⟦ ρ ⟧ʳ θ ⟩

infix 4 _⊨ᴴ_

record _⊨ᴴ_ {Θ : Scope} (θ : Grounding Θ) (Q : Hyps Θ) : Set where
  constructor mk⊨ᴴ
  field
    etOK   : ∀ {α} → α ∈ ets Q → Eternal (gTy θ α)
    subOK  : ∀ {α β} → (α , β) ∈ subᵥ Q → gTy θ α <:ᵛ gTy θ β
    ordROK : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
    ordEOK : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ
    disjOK : ∀ {A ρ} → (A , ρ) ∈ disj Q
           → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)

open _⊨ᴴ_ public

-- Every grounding satisfies the empty hypothesis set

∅ᴴ-⊨ : ∀ {Θ} {θ : Grounding Θ} → θ ⊨ᴴ ∅ᴴ
∅ᴴ-⊨ = mk⊨ᴴ (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

ground-≡̂ᵣ : ∀ {Θ} {θ : Grounding Θ} {ρ ρ' : RExp Θ}
          → ρ ≡̂ᵣ ρ' → ⟦ ρ ⟧ʳ θ ≡ ⟦ ρ' ⟧ʳ θ
ground-≡̂ₑ : ∀ {Θ} {θ : Grounding Θ} {ε ε' : EExp Θ}
          → ε ≡̂ₑ ε' → ⟦ ε ⟧ᵉ θ ≡ ⟦ ε' ⟧ᵉ θ

ground-≡̂ᵣ ≡̂ᵣ-refl          = refl
ground-≡̂ᵣ (≡̂ᵣ-sym p)       = sym (ground-≡̂ᵣ p)
ground-≡̂ᵣ (≡̂ᵣ-trans p q)   = trans (ground-≡̂ᵣ p) (ground-≡̂ᵣ q)
ground-≡̂ᵣ (≡̂ᵣ-cong p q)    = cong₂ _·ᵣ_ (ground-≡̂ᵣ p) (ground-≡̂ᵣ q)
ground-≡̂ᵣ ≡̂ᵣ-assoc         = ·ᵣ-assoc _ _ _
ground-≡̂ᵣ ≡̂ᵣ-identityˡ     = ·ᵣ-identityˡ _
ground-≡̂ᵣ ≡̂ᵣ-identityʳ     = ·ᵣ-identityʳ _
ground-≡̂ᵣ ≡̂ᵣ-const-·       = refl
ground-≡̂ᵣ (≡̂ᵣ-cong-⊔ p q)  = cong₂ _⊔ᵣ_ (ground-≡̂ᵣ p) (ground-≡̂ᵣ q)
ground-≡̂ᵣ ≡̂ᵣ-const-⊔       = refl
ground-≡̂ᵣ ≡̂ᵣ-map-·         = map-·ᵉ
ground-≡̂ᵣ ≡̂ᵣ-map-⊔         = map-⊔ᵉ
ground-≡̂ᵣ ≡̂ᵣ-map-const     = refl
ground-≡̂ᵣ (≡̂ᵣ-map-cong p)  = cong mapᵉ (ground-≡̂ₑ p)

ground-≡̂ₑ ≡̂ₑ-refl        = refl
ground-≡̂ₑ (≡̂ₑ-sym p)     = sym (ground-≡̂ₑ p)
ground-≡̂ₑ (≡̂ₑ-trans p q) = trans (ground-≡̂ₑ p) (ground-≡̂ₑ q)
ground-≡̂ₑ (≡̂ₑ-cong p q)  = cong₂ _·ₑ_ (ground-≡̂ₑ p) (ground-≡̂ₑ q)
ground-≡̂ₑ ≡̂ₑ-assoc       = ·ₑ-assoc _ _ _
ground-≡̂ₑ ≡̂ₑ-identityˡ   = ·ₑ-identityˡ _
ground-≡̂ₑ ≡̂ₑ-identityʳ   = ·ₑ-identityʳ _
ground-≡̂ₑ ≡̂ₑ-const-·     = refl
ground-≡̂ₑ (≡̂ₑ-cong-⊔ p q) = cong₂ _⊔ₑ_ (ground-≡̂ₑ p) (ground-≡̂ₑ q)
ground-≡̂ₑ ≡̂ₑ-const-⊔     = refl

ground-≾ᵣ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {ρ ρ' : RExp Θ}
          → θ ⊨ᴴ Q → Q ⊩ ρ ≾̂ᵣ ρ' → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
ground-≾ₑ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {ε ε' : EExp Θ}
          → θ ⊨ᴴ Q → Q ⊩ ε ≾̂ₑ ε' → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ

ground-≾ᵣ h (hypᵣ m)     = ordROK h m
ground-≾ᵣ h (atomᵣ p)    = p
ground-≾ᵣ h (eqᵣ p)      = ≾ᵣ-reflexive (ground-≡̂ᵣ p)
ground-≾ᵣ h (transᵣ p q) = ≾ᵣ-trans (ground-≾ᵣ h p) (ground-≾ᵣ h q)
ground-≾ᵣ h (monoᵣ p q)  = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (ground-≾ᵣ h p))
                                    (·ᵣ-monoʳ-≾ᵣ (ground-≾ᵣ h q))
ground-≾ᵣ h (map-mono p) = map-monotoneᵉ (ground-≾ₑ h p)
ground-≾ᵣ {θ = θ} h (⊔-ubˡᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubˡ (⟦ ρ₁ ⟧ʳ θ) (⟦ ρ₂ ⟧ʳ θ)
ground-≾ᵣ {θ = θ} h (⊔-ubʳᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubʳ (⟦ ρ₁ ⟧ʳ θ) (⟦ ρ₂ ⟧ʳ θ)
ground-≾ᵣ h (⊔-lubᵣ p q) = ⊔ᵣ-lub (ground-≾ᵣ h p) (ground-≾ᵣ h q)
ground-≾ᵣ {θ = θ} h (·-distribˡ-⊔ᵣ {ρ} {ρ₁} {ρ₂}) =
  ·ᵣ-distribˡ-⊔ᵣ-≾ᵣ (⟦ ρ ⟧ʳ θ) (⟦ ρ₁ ⟧ʳ θ) (⟦ ρ₂ ⟧ʳ θ)
ground-≾ᵣ {θ = θ} h (·-distribʳ-⊔ᵣ {ρ} {ρ₁} {ρ₂}) =
  ·ᵣ-distribʳ-⊔ᵣ-≾ᵣ (⟦ ρ ⟧ʳ θ) (⟦ ρ₁ ⟧ʳ θ) (⟦ ρ₂ ⟧ʳ θ)
ground-≾ᵣ {θ = θ} {ρ' = ρ'} h (minᵣ p) = p (⟦ ρ' ⟧ʳ θ)

ground-≾ₑ h (hypₑ m)     = ordEOK h m
ground-≾ₑ h (atomₑ p)    = p
ground-≾ₑ h (eqₑ p)      = ≾ₑ-reflexive (ground-≡̂ₑ p)
ground-≾ₑ h (transₑ p q) = ≾ₑ-trans (ground-≾ₑ h p) (ground-≾ₑ h q)
ground-≾ₑ h (monoₑ p q)  = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (ground-≾ₑ h p))
                                    (·ₑ-monoʳ-≾ₑ (ground-≾ₑ h q))
ground-≾ₑ {θ = θ} h (⊔-ubˡₑ {ε₁} {ε₂}) = ⊔ₑ-ubˡ (⟦ ε₁ ⟧ᵉ θ) (⟦ ε₂ ⟧ᵉ θ)
ground-≾ₑ {θ = θ} h (⊔-ubʳₑ {ε₁} {ε₂}) = ⊔ₑ-ubʳ (⟦ ε₁ ⟧ᵉ θ) (⟦ ε₂ ⟧ᵉ θ)
ground-≾ₑ h (⊔-lubₑ p q) = ⊔ₑ-lub (ground-≾ₑ h p) (ground-≾ₑ h q)
ground-≾ₑ {θ = θ} h (·-distribˡ-⊔ₑ {ε} {ε₁} {ε₂}) =
  ·ₑ-distribˡ-⊔ₑ-≾ₑ (⟦ ε ⟧ᵉ θ) (⟦ ε₁ ⟧ᵉ θ) (⟦ ε₂ ⟧ᵉ θ)
ground-≾ₑ {θ = θ} h (·-distribʳ-⊔ₑ {ε} {ε₁} {ε₂}) =
  ·ₑ-distribʳ-⊔ₑ-≾ₑ (⟦ ε ⟧ᵉ θ) (⟦ ε₁ ⟧ᵉ θ) (⟦ ε₂ ⟧ᵉ θ)
ground-≾ₑ {θ = θ} {ε' = ε'} h (minₑ p) = p (⟦ ε' ⟧ᵉ θ)

-- An assumed subtyping between type variables grounds to a closed
-- subtyping between their images.

ground-⊩ᵗᵛ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {α β}
           → θ ⊨ᴴ Q → Q ⊩ᵗᵛ α ≾ β → gTy θ α <:ᵛ gTy θ β
ground-⊩ᵗᵛ {θ = θ} h (reflᵗᵛ {α}) = <:ᵛ-refl (gTy θ α)
ground-⊩ᵗᵛ         h (hypᵗᵛ m)     = subOK h m
ground-⊩ᵗᵛ         h (transᵗᵛ p q) = <:ᵛ-trans (ground-⊩ᵗᵛ h p) (ground-⊩ᵗᵛ h q)

ground-Et : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {A : OVType Θ}
          → θ ⊨ᴴ Q → Q ⊩ᴱ A → Eternal (⟦ A ⟧ᵛ θ)
ground-Et h (et-hyp m)       = etOK h m
ground-Et h (et-subˡ p et)   = <:ᵛ-eternalˡ (ground-⊩ᵗᵛ h p) (ground-Et h et)
ground-Et h (et-subʳ p et)   = <:ᵛ-eternalʳ (ground-⊩ᵗᵛ h p) (ground-Et h et)
ground-Et h (Baseₑ p)        = Baseₑ p
ground-Et h Unitₑ            = Unitₑ
ground-Et h Boolₑ            = Boolₑ
ground-Et h (et₁ |×|ₑ et₂)   = ground-Et h et₁ |×|ₑ ground-Et h et₂
ground-Et h Emptyₑ           = Emptyₑ

-- Subtyping grounds structurally: each constructor maps to its closed
-- counterpart, the grade slots by `ground-≾ᵣ`/`ground-≾ₑ` and the
-- variable heads by `ground-⊩ᵗᵛ`.

ground-<:ᵛ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {A A' : OVType Θ}
           → θ ⊨ᴴ Q → Q ∣ A <:̂ᵛ A' → ⟦ A ⟧ᵛ θ <:ᵛ ⟦ A' ⟧ᵛ θ
ground-<:ᶜ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {C C' : OCType Θ}
           → θ ⊨ᴴ Q → Q ∣ C <:̂ᶜ C' → ⟦ C ⟧ᶜ θ <:ᶜ ⟦ C' ⟧ᶜ θ

ground-<:ᵛ         h (tvarₛ p)        = ground-⊩ᵗᵛ h p
ground-<:ᵛ         h (Baseₛ p)        = Baseₛ p
ground-<:ᵛ         h Unitₛ            = Unitₛ
ground-<:ᵛ         h Boolₛ            = Boolₛ
ground-<:ᵛ         h (p |×|ₛ r)       = ground-<:ᵛ h p |×|ₛ ground-<:ᵛ h r
ground-<:ᵛ         h Emptyₛ           = Emptyₛ
ground-<:ᵛ         h (p ⇒ₛ r)         = ground-<:ᵛ h p ⇒ₛ ground-<:ᶜ h r
ground-<:ᵛ         h ([ q ]ₛ p)       = [ ground-≾ᵣ h q ]ₛ ground-<:ᵛ h p

ground-<:ᶜ h (p ‼ₛ q) = ground-<:ᵛ h p ‼ₛ ground-≾ₑ h q

-- Each membership former maps to its counterpart.

ground-∈ : ∀ {Θ n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
         → (θ : Grounding Θ) → A ∈̂[ ρ ] Γ
         → ⟦ A ⟧ᵛ θ ∈[ ⟦ ρ ⟧ʳ θ ] ⟦ Γ ⟧ᶜᵗˣ θ
ground-∈ θ Hd        = Hd
ground-∈ θ (Tl-∷ x)  = Tl-∷ (ground-∈ θ x)
ground-∈ θ (Tl-⟨⟩ x) = Tl-⟨⟩ (ground-∈ θ x)

ground-VarOK : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {A : OVType Θ} {ρ : RExp Θ}
             → θ ⊨ᴴ Q → VarOK Q A ρ
             → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
ground-VarOK h (et-ok et) = inj₁ (ground-Et h et)
ground-VarOK h (≾ᵘ-ok le) = inj₂ (ground-≾ᵣ h le)
ground-VarOK h (hyp-ok m) = disjOK h m

ground-var : ∀ {Θ n} {Q : Hyps Θ} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
           → (θ : Grounding Θ) → θ ⊨ᴴ Q
           → (x : A ∈̂[ ρ ] Γ) → VarOK Q A ρ
           → ( (¬ Eternal (⟦ A ⟧ᵛ θ) → ⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
             × (⟦ A ⟧ᵛ θ ∈[ ⟦ ρ ⟧ʳ θ ] ⟦ Γ ⟧ᶜᵗˣ θ))
ground-var θ h x ok =
  [ (λ et ¬et → ⊥-elim (¬et et)) , (λ le _ → le) ]′ (ground-VarOK h ok) ,
  ground-∈ θ x

ground-unbox : ∀ {Θ n} {Q : Hyps Θ} {A : OVType Θ} {ρ ρ' : RExp Θ} {Γ : OCtx Θ n}
             → (θ : Grounding Θ) → θ ⊨ᴴ Q
             → (x : [ ρ ] A ∈̂[ ρ' ] Γ) → Q ⊩ ρ' ≾̂ᵣ ρ
             → (⟦ ρ' ⟧ʳ θ ≾ᵣ ⟦ ρ ⟧ʳ θ)
             × ([ ⟦ ρ ⟧ʳ θ ] ⟦ A ⟧ᵛ θ ∈[ ⟦ ρ' ⟧ʳ θ ] ⟦ Γ ⟧ᶜᵗˣ θ)
ground-unbox θ h x le = ground-≾ᵣ h le , ground-∈ θ x

mutual

  ⌜⌝ᵛ-ground : ∀ {Θ} {θ : Grounding Θ} → (A : VType) → ⟦ ⌜ A ⌝ᵛ ⟧ᵛ θ ≡ A
  ⌜⌝ᵛ-ground (Base b)   = refl
  ⌜⌝ᵛ-ground Unit       = refl
  ⌜⌝ᵛ-ground Bool       = refl
  ⌜⌝ᵛ-ground (A |×| B)  = cong₂ _|×|_ (⌜⌝ᵛ-ground A) (⌜⌝ᵛ-ground B)
  ⌜⌝ᵛ-ground Empty      = refl
  ⌜⌝ᵛ-ground (A ⇒ C)    = cong₂ _⇒_ (⌜⌝ᵛ-ground A) (⌜⌝ᶜ-ground C)
  ⌜⌝ᵛ-ground ([ ρ ] A)  = cong [ ρ ]_ (⌜⌝ᵛ-ground A)

  ⌜⌝ᶜ-ground : ∀ {Θ} {θ : Grounding Θ} → (C : CType) → ⟦ ⌜ C ⌝ᶜ ⟧ᶜ θ ≡ C
  ⌜⌝ᶜ-ground (A ‼ ε) = cong (_‼ ε) (⌜⌝ᵛ-ground A)

⌜⌝ᵍ-ground : ∀ {Θ} {θ : Grounding Θ} → (G : GType) → ⟦ ⌜ G ⌝ᵍ ⟧ᵛ θ ≡ type-of-gtype G
⌜⌝ᵍ-ground (Base b)    = refl
⌜⌝ᵍ-ground Unit        = refl
⌜⌝ᵍ-ground Bool        = refl
⌜⌝ᵍ-ground Empty       = refl
⌜⌝ᵍ-ground (A |×|ᵍ B)  = cong₂ _|×|_ (⌜⌝ᵍ-ground A) (⌜⌝ᵍ-ground B)
⌜⌝ᵍ-ground ([ ρ ]ᵍ A)  = cong [ ρ ]_ (⌜⌝ᵍ-ground A)

-- Weakening into `Θ +e` and grounding the new variable away is the
-- identity on interpretations; needed by the `handle` case.

ground-wkᵉ-e : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (ε : EExp Θ)
             → ⟦ wkᵉ-e ε ⟧ᵉ (θ ,ᵍᵉ ε₀) ≡ ⟦ ε ⟧ᵉ θ
ground-wkᵉ-e (evar i)   = refl
ground-wkᵉ-e (econst ε) = refl
ground-wkᵉ-e (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (ground-wkᵉ-e ε) (ground-wkᵉ-e ε')
ground-wkᵉ-e (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (ground-wkᵉ-e ε) (ground-wkᵉ-e ε')

ground-wkᵉ-r : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (ρ : RExp Θ)
             → ⟦ wkᵉ-r ρ ⟧ʳ (θ ,ᵍᵉ ε₀) ≡ ⟦ ρ ⟧ʳ θ
ground-wkᵉ-r (rvar i)   = refl
ground-wkᵉ-r (rconst ρ) = refl
ground-wkᵉ-r (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (ground-wkᵉ-r ρ) (ground-wkᵉ-r ρ')
ground-wkᵉ-r (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (ground-wkᵉ-r ρ) (ground-wkᵉ-r ρ')
ground-wkᵉ-r ∣ ε ∣̂ᵉ     = cong mapᵉ (ground-wkᵉ-e ε)

mutual

  ground-wkᵉ-v : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (A : OVType Θ)
               → ⟦ wkᵉ-v A ⟧ᵛ (θ ,ᵍᵉ ε₀) ≡ ⟦ A ⟧ᵛ θ
  ground-wkᵉ-v (tvar α)  = refl
  ground-wkᵉ-v (Base b)  = refl
  ground-wkᵉ-v Unit      = refl
  ground-wkᵉ-v Bool      = refl
  ground-wkᵉ-v (A |×| B) = cong₂ _|×|_ (ground-wkᵉ-v A) (ground-wkᵉ-v B)
  ground-wkᵉ-v Empty     = refl
  ground-wkᵉ-v (A ⇒ C)   = cong₂ _⇒_ (ground-wkᵉ-v A) (ground-wkᵉ-c C)
  ground-wkᵉ-v ([ ρ ] A) = cong₂ [_]_ (ground-wkᵉ-r ρ) (ground-wkᵉ-v A)

  ground-wkᵉ-c : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (C : OCType Θ)
               → ⟦ wkᵉ-c C ⟧ᶜ (θ ,ᵍᵉ ε₀) ≡ ⟦ C ⟧ᶜ θ
  ground-wkᵉ-c (A ‼ ε) = cong₂ _‼_ (ground-wkᵉ-v A) (ground-wkᵉ-e ε)

ground-wkᵉ-ctx : ∀ {Θ n} {θ : Grounding Θ} {ε₀ : E} → (Γ : OCtx Θ n)
               → ⟦ wkᵉ-ctx Γ ⟧ᶜᵗˣ (θ ,ᵍᵉ ε₀) ≡ ⟦ Γ ⟧ᶜᵗˣ θ
ground-wkᵉ-ctx []        = refl
ground-wkᵉ-ctx (Γ ∷ A)   = cong₂ _∷_ (ground-wkᵉ-ctx Γ) (ground-wkᵉ-v A)
ground-wkᵉ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (ground-wkᵉ-ctx Γ) (ground-wkᵉ-r ρ)

-- An extended grounding satisfies the weakened hypothesis set

⊨ᴴ-wkᵉ-ground : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {ε₀ : E}
              → θ ⊨ᴴ Q → (θ ,ᵍᵉ ε₀) ⊨ᴴ wkᵉ-H Q
⊨ᴴ-wkᵉ-ground {Θ} {θ} {Q} {ε₀} h = mk⊨ᴴ et sub ordR ordE dsj
  where
    et : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Eternal (gTy (θ ,ᵍᵉ ε₀) α)
    et m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | α₀ , m₀ , refl = etOK h m₀

    sub : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q)
        → gTy (θ ,ᵍᵉ ε₀) α <:ᵛ gTy (θ ,ᵍᵉ ε₀) β
    sub m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | (α₀ , β₀) , m₀ , refl = subOK h m₀

    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
         → ⟦ ρ ⟧ʳ (θ ,ᵍᵉ ε₀) ≾ᵣ ⟦ ρ' ⟧ʳ (θ ,ᵍᵉ ε₀)
    ordR m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ _≾ᵣ_ (sym (ground-wkᵉ-r ρ₀)) (sym (ground-wkᵉ-r ρ₀')) (ordROK h m₀)

    ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
         → ⟦ ε ⟧ᵉ (θ ,ᵍᵉ ε₀) ≾ₑ ⟦ ε' ⟧ᵉ (θ ,ᵍᵉ ε₀)
    ordE m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀' , ε₀'') , m₀ , refl =
      subst₂ _≾ₑ_ (sym (ground-wkᵉ-e ε₀')) (sym (ground-wkᵉ-e ε₀'')) (ordEOK h m₀)

    dsj : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q)
        → Eternal (⟦ A ⟧ᵛ (θ ,ᵍᵉ ε₀)) ⊎ (⟦ ρ ⟧ʳ (θ ,ᵍᵉ ε₀) ≾ᵣ uᵣ)
    dsj m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      [ (λ et → inj₁ (subst Eternal (sym (ground-wkᵉ-v A₀)) et))
      , (λ le → inj₂ (subst (_≾ᵣ uᵣ) (sym (ground-wkᵉ-r ρ₀)) le)) ]′ (disjOK h m₀)
