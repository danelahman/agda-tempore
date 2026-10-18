------------------------------------------------------------------
-- Declarative satisfaction of hypotheses                       --
--                                                              --
-- A declarative instance `σ` satisfies `Q` (`σ ⊨ᴰ Q`) when     --
-- each atom of `Q` holds in the closed calculus at its         --
-- interpretation: an eternality atom as `Eternal`, a subtyping --
-- atom as `_<:ᵛ_`, an ordering in the grade's order, and a     --
-- var-rule disjunction as a sum.                               --
--                                                              --
-- Entailment is sound for it: what `Q` entails holds at every  --
-- instance satisfying `Q` (`sound-≾ᵣ`, `sound-≾ₑ`, `sound-⊩ᴱ`, --
-- `sound-<:ᵛ`, `sound-<:ᶜ`, `sound-VarOK`). A membership in an --
-- open context is one in its interpretation (`⟦_⟧ˣ`), and a    --
-- handler clause's weakened hypotheses hold at every extension --
-- of a satisfying instance (`⊨ᴰ-,ᵉ`).                          --
------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Maybe using (to-witness)
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module Instantiation.Judgements (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Subtyping S
import Syntax.Erasure S as CE

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (_+eⁿ_; Oblig; Obligs; rigids; body)

open import Instantiation.Types S

------------------------------------------------------------------------
-- Satisfaction

infix 4 _⊨ᴰ_

record _⊨ᴰ_ {Θ : Scope} (σ : DInst Θ) (Q : Hyps Θ) : Set where
  constructor mk⊨ᴰ
  field
    ⊨ets  : ∀ {α} → α ∈ ets Q → Eternal (ty σ α)
    ⊨subᵥ : ∀ {α β} → (α , β) ∈ subᵥ Q → ty σ α <:ᵛ ty σ β
    ⊨ordᵣ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
    ⊨ordₑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ
    ⊨disj : ∀ {A ρ} → (A , ρ) ∈ disj Q → Eternal (⟦ A ⟧ᵛ σ) ⊎ (⟦ ρ ⟧ʳ σ ≾ᵣ uᵣ)

open _⊨ᴰ_ public

⊨ᴰ-∅ : ∀ {Θ} {σ : DInst Θ} → σ ⊨ᴰ ∅ᴴ
⊨ᴰ-∅ = mk⊨ᴰ (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- An obligation `∀ᵉ j₁ … jₖ. B` holds when `B` does at every extension
-- by grades for its rigids

infix 4 _⊨ᴰ⟨_⟩_ _⊨ᴰᴼ_ _⊨ᴰᴿ_

_⊨ᴰ⟨_⟩_ : ∀ {Θ} → DInst Θ → (k : ℕ) → Hyps (Θ +eⁿ k) → Set
σ ⊨ᴰ⟨ zero ⟩  B = σ ⊨ᴰ B
σ ⊨ᴰ⟨ suc k ⟩ B = (c : E) → (σ ,ᵉᴰ c) ⊨ᴰ⟨ k ⟩ B

_⊨ᴰᴼ_ : ∀ {Θ} → DInst Θ → Oblig Θ → Set
σ ⊨ᴰᴼ O = σ ⊨ᴰ⟨ rigids O ⟩ body O

_⊨ᴰᴿ_ : ∀ {Θ} → DInst Θ → Obligs Θ → Set
σ ⊨ᴰᴿ R = All (σ ⊨ᴰᴼ_) R

------------------------------------------------------------------------
-- Soundness of convertibility and entailed ordering

sound-≡̂ᵣ : ∀ {Θ} {ρ ρ' : RExp Θ} → (σ : DInst Θ) → ρ ≡̂ᵣ ρ' → ⟦ ρ ⟧ʳ σ ≡ ⟦ ρ' ⟧ʳ σ
sound-≡̂ₑ : ∀ {Θ} {ε ε' : EExp Θ} → (σ : DInst Θ) → ε ≡̂ₑ ε' → ⟦ ε ⟧ᵉ σ ≡ ⟦ ε' ⟧ᵉ σ
sound-≾ᵣ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} {ρ ρ' : RExp Θ}
         → σ ⊨ᴰ Q → Q ⊩ ρ ≾̂ᵣ ρ' → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
sound-≾ₑ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} {ε ε' : EExp Θ}
         → σ ⊨ᴰ Q → Q ⊩ ε ≾̂ₑ ε' → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ

sound-≡̂ᵣ σ ≡̂ᵣ-refl          = refl
sound-≡̂ᵣ σ (≡̂ᵣ-sym p)       = sym (sound-≡̂ᵣ σ p)
sound-≡̂ᵣ σ (≡̂ᵣ-trans p q)   = trans (sound-≡̂ᵣ σ p) (sound-≡̂ᵣ σ q)
sound-≡̂ᵣ σ (≡̂ᵣ-cong p q)    = cong₂ _·ᵣ_ (sound-≡̂ᵣ σ p) (sound-≡̂ᵣ σ q)
sound-≡̂ᵣ σ ≡̂ᵣ-assoc         = ·ᵣ-assoc _ _ _
sound-≡̂ᵣ σ ≡̂ᵣ-identityˡ     = ·ᵣ-identityˡ _
sound-≡̂ᵣ σ ≡̂ᵣ-identityʳ     = ·ᵣ-identityʳ _
sound-≡̂ᵣ σ ≡̂ᵣ-const-·       = refl
sound-≡̂ᵣ σ (≡̂ᵣ-comm ij)     = to-witness ij _ _
sound-≡̂ᵣ σ (≡̂ᵣ-cong-⊔ p q)  = cong₂ _⊔ᵣ_ (sound-≡̂ᵣ σ p) (sound-≡̂ᵣ σ q)
sound-≡̂ᵣ σ ≡̂ᵣ-const-⊔       = refl
sound-≡̂ᵣ σ ≡̂ᵣ-comm-⊔        = ⊔ᵣ-comm _ _
sound-≡̂ᵣ σ ≡̂ᵣ-distribˡ-⊔    = ·ᵣ-distribˡ-⊔ᵣ _ _ _
sound-≡̂ᵣ σ ≡̂ᵣ-distribʳ-⊔    = ·ᵣ-distribʳ-⊔ᵣ _ _ _
sound-≡̂ᵣ σ ≡̂ᵣ-map-·         = map-·ᵉ
sound-≡̂ᵣ σ ≡̂ᵣ-map-⊔         = map-⊔ᵉ
sound-≡̂ᵣ σ ≡̂ᵣ-map-const     = refl
sound-≡̂ᵣ σ (≡̂ᵣ-map-cong p)  = cong mapᵉ (sound-≡̂ₑ σ p)
sound-≡̂ᵣ σ (≡̂ᵣ-absorb p)    = ⊔ᵣ-absorb (sound-≾ᵣ (⊨ᴰ-∅ {σ = σ}) p)

sound-≡̂ₑ σ ≡̂ₑ-refl          = refl
sound-≡̂ₑ σ (≡̂ₑ-sym p)       = sym (sound-≡̂ₑ σ p)
sound-≡̂ₑ σ (≡̂ₑ-trans p q)   = trans (sound-≡̂ₑ σ p) (sound-≡̂ₑ σ q)
sound-≡̂ₑ σ (≡̂ₑ-cong p q)    = cong₂ _·ₑ_ (sound-≡̂ₑ σ p) (sound-≡̂ₑ σ q)
sound-≡̂ₑ σ ≡̂ₑ-assoc         = ·ₑ-assoc _ _ _
sound-≡̂ₑ σ ≡̂ₑ-identityˡ     = ·ₑ-identityˡ _
sound-≡̂ₑ σ ≡̂ₑ-identityʳ     = ·ₑ-identityʳ _
sound-≡̂ₑ σ ≡̂ₑ-const-·       = refl
sound-≡̂ₑ σ (≡̂ₑ-comm ij)     = to-witness ij _ _
sound-≡̂ₑ σ (≡̂ₑ-cong-⊔ p q)  = cong₂ _⊔ₑ_ (sound-≡̂ₑ σ p) (sound-≡̂ₑ σ q)
sound-≡̂ₑ σ ≡̂ₑ-const-⊔       = refl
sound-≡̂ₑ σ ≡̂ₑ-comm-⊔        = ⊔ₑ-comm _ _
sound-≡̂ₑ σ ≡̂ₑ-distribˡ-⊔    = ·ₑ-distribˡ-⊔ₑ _ _ _
sound-≡̂ₑ σ ≡̂ₑ-distribʳ-⊔    = ·ₑ-distribʳ-⊔ₑ _ _ _
sound-≡̂ₑ σ (≡̂ₑ-absorb p)    = ⊔ₑ-absorb (sound-≾ₑ (⊨ᴰ-∅ {σ = σ}) p)

sound-≾ᵣ s (hypᵣ m)     = ⊨ordᵣ s m
sound-≾ᵣ s (atomᵣ p)    = p
sound-≾ᵣ {σ = σ} s (eqᵣ p) = ≾ᵣ-reflexive (sound-≡̂ᵣ σ p)
sound-≾ᵣ s (transᵣ p q) = ≾ᵣ-trans (sound-≾ᵣ s p) (sound-≾ᵣ s q)
sound-≾ᵣ s (monoᵣ p q)  = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (sound-≾ᵣ s p)) (·ᵣ-monoʳ-≾ᵣ (sound-≾ᵣ s q))
sound-≾ᵣ s (map-mono p) = map-monotoneᵉ (sound-≾ₑ s p)
sound-≾ᵣ {σ = σ} s (⊔-ubˡᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubˡ (⟦ ρ₁ ⟧ʳ σ) (⟦ ρ₂ ⟧ʳ σ)
sound-≾ᵣ {σ = σ} s (⊔-ubʳᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubʳ (⟦ ρ₁ ⟧ʳ σ) (⟦ ρ₂ ⟧ʳ σ)
sound-≾ᵣ s (⊔-lubᵣ p q) = ⊔ᵣ-lub (sound-≾ᵣ s p) (sound-≾ᵣ s q)
sound-≾ᵣ {σ = σ} s (topᵣ {ρ}) = ≾-⊤ᵣ (⟦ ρ ⟧ʳ σ)
sound-≾ᵣ {σ = σ} {ρ' = ρ'} s (minᵣ ij) = to-witness ij (⟦ ρ' ⟧ʳ σ)
sound-≾ᵣ s (zeroˡᵣ p)   = ≾ᵣ-zero-productˡ (sound-≾ᵣ s p)
sound-≾ᵣ s (zeroʳᵣ p)   = ≾ᵣ-zero-productʳ (sound-≾ᵣ s p)
sound-≾ᵣ s (plusᵣ p q r) = Plus.c⁺-least p (sound-≾ᵣ s q) (sound-≾ᵣ s r)
sound-≾ᵣ s (indˡᵣ p q)  = Plus.⁺-indˡ p (sound-≾ᵣ s q)
sound-≾ᵣ s (indʳᵣ p q)  = Plus.⁺-indʳ p (sound-≾ᵣ s q)

sound-≾ₑ s (hypₑ m)     = ⊨ordₑ s m
sound-≾ₑ s (atomₑ p)    = p
sound-≾ₑ {σ = σ} s (eqₑ p) = ≾ₑ-reflexive (sound-≡̂ₑ σ p)
sound-≾ₑ s (transₑ p q) = ≾ₑ-trans (sound-≾ₑ s p) (sound-≾ₑ s q)
sound-≾ₑ s (monoₑ p q)  = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (sound-≾ₑ s p)) (·ₑ-monoʳ-≾ₑ (sound-≾ₑ s q))
sound-≾ₑ {σ = σ} s (⊔-ubˡₑ {ε₁} {ε₂}) = ⊔ₑ-ubˡ (⟦ ε₁ ⟧ᵉ σ) (⟦ ε₂ ⟧ᵉ σ)
sound-≾ₑ {σ = σ} s (⊔-ubʳₑ {ε₁} {ε₂}) = ⊔ₑ-ubʳ (⟦ ε₁ ⟧ᵉ σ) (⟦ ε₂ ⟧ᵉ σ)
sound-≾ₑ s (⊔-lubₑ p q) = ⊔ₑ-lub (sound-≾ₑ s p) (sound-≾ₑ s q)
sound-≾ₑ {σ = σ} s (topₑ {ε}) = ≾-⊤ₑ (⟦ ε ⟧ᵉ σ)
sound-≾ₑ {σ = σ} {ε' = ε'} s (minₑ ij) = to-witness ij (⟦ ε' ⟧ᵉ σ)
sound-≾ₑ s (zeroˡₑ p)   = ≾ₑ-zero-productˡ (sound-≾ₑ s p)
sound-≾ₑ s (zeroʳₑ p)   = ≾ₑ-zero-productʳ (sound-≾ₑ s p)
sound-≾ₑ s (plusₑ p q r) = Plus.c⁺-least p (sound-≾ₑ s q) (sound-≾ₑ s r)
sound-≾ₑ s (indˡₑ p q)  = Plus.⁺-indˡ p (sound-≾ₑ s q)
sound-≾ₑ s (indʳₑ p q)  = Plus.⁺-indʳ p (sound-≾ₑ s q)

------------------------------------------------------------------------
-- Soundness of the type-level judgements

-- Convertible types mean the same type

sound-≡̂ᵛ : ∀ {Θ} {A A' : OVType Θ} → (σ : DInst Θ) → A ≡̂ᵛ A' → ⟦ A ⟧ᵛ σ ≡ ⟦ A' ⟧ᵛ σ
sound-≡̂ᶜ : ∀ {Θ} {C C' : OCType Θ} → (σ : DInst Θ) → C ≡̂ᶜ C' → ⟦ C ⟧ᶜ σ ≡ ⟦ C' ⟧ᶜ σ

sound-≡̂ᵛ σ tvar≡̂       = refl
sound-≡̂ᵛ σ Base≡̂       = refl
sound-≡̂ᵛ σ Unit≡̂       = refl
sound-≡̂ᵛ σ Bool≡̂       = refl
sound-≡̂ᵛ σ Nat≡̂        = refl
sound-≡̂ᵛ σ (p |×|≡̂ q)  = cong₂ _|×|_ (sound-≡̂ᵛ σ p) (sound-≡̂ᵛ σ q)
sound-≡̂ᵛ σ (p |+|≡̂ q)  = cong₂ _|+|_ (sound-≡̂ᵛ σ p) (sound-≡̂ᵛ σ q)
sound-≡̂ᵛ σ (|List|≡̂ p) = cong |List| (sound-≡̂ᵛ σ p)
sound-≡̂ᵛ σ Empty≡̂      = refl
sound-≡̂ᵛ σ (p ⇒≡̂ q)    = cong₂ _⇒_ (sound-≡̂ᵛ σ p) (sound-≡̂ᶜ σ q)
sound-≡̂ᵛ σ ([ r ]≡̂ p)  = cong₂ [_]_ (sound-≡̂ᵣ σ r) (sound-≡̂ᵛ σ p)

sound-≡̂ᶜ σ (p ‼≡̂ e) = cong₂ _‼_ (sound-≡̂ᵛ σ p) (sound-≡̂ₑ σ e)

module _ {Θ : Scope} {σ : DInst Θ} {Q : Hyps Θ} (s : σ ⊨ᴰ Q) where

  sound-⊩ᵗᵛ : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → ty σ α <:ᵛ ty σ β
  sound-⊩ᵗᵛ (reflᵗᵛ {α})  = <:ᵛ-refl (ty σ α)
  sound-⊩ᵗᵛ (hypᵗᵛ m)     = ⊨subᵥ s m
  sound-⊩ᵗᵛ (transᵗᵛ p q) = <:ᵛ-trans (sound-⊩ᵗᵛ p) (sound-⊩ᵗᵛ q)

  sound-⊩ᴱ : {A : OVType Θ} → Q ⊩ᴱ A → Eternal (⟦ A ⟧ᵛ σ)
  sound-⊩ᴱ (et-hyp m)     = ⊨ets s m
  sound-⊩ᴱ (et-subˡ p et) = <:ᵛ-eternalˡ (sound-⊩ᵗᵛ p) (sound-⊩ᴱ et)
  sound-⊩ᴱ (et-subʳ p et) = <:ᵛ-eternalʳ (sound-⊩ᵗᵛ p) (sound-⊩ᴱ et)
  sound-⊩ᴱ (Baseₑ p)      = Baseₑ p
  sound-⊩ᴱ Unitₑ          = Unitₑ
  sound-⊩ᴱ Boolₑ          = Boolₑ
  sound-⊩ᴱ Natₑ           = Natₑ
  sound-⊩ᴱ (p |×|ₑ q)     = sound-⊩ᴱ p |×|ₑ sound-⊩ᴱ q
  sound-⊩ᴱ (p |+|ₑ q)     = sound-⊩ᴱ p |+|ₑ sound-⊩ᴱ q
  sound-⊩ᴱ (|List|ₑ p)    = |List|ₑ (sound-⊩ᴱ p)
  sound-⊩ᴱ Emptyₑ         = Emptyₑ

  sound-<:ᵛ : {A B : OVType Θ} → Q ∣ A <:̂ᵛ B → ⟦ A ⟧ᵛ σ <:ᵛ ⟦ B ⟧ᵛ σ
  sound-<:ᶜ : {C D : OCType Θ} → Q ∣ C <:̂ᶜ D → ⟦ C ⟧ᶜ σ <:ᶜ ⟦ D ⟧ᶜ σ

  sound-<:ᵛ (tvarₛ p)   = sound-⊩ᵗᵛ p
  sound-<:ᵛ (Baseₛ p)   = Baseₛ p
  sound-<:ᵛ Unitₛ       = Unitₛ
  sound-<:ᵛ Boolₛ       = Boolₛ
  sound-<:ᵛ Natₛ        = Natₛ
  sound-<:ᵛ (p |×|ₛ q)  = sound-<:ᵛ p |×|ₛ sound-<:ᵛ q
  sound-<:ᵛ (p |+|ₛ q)  = sound-<:ᵛ p |+|ₛ sound-<:ᵛ q
  sound-<:ᵛ (|List|ₛ p) = |List|ₛ (sound-<:ᵛ p)
  sound-<:ᵛ Emptyₛ      = Emptyₛ
  sound-<:ᵛ (p ⇒ₛ q)    = sound-<:ᵛ p ⇒ₛ sound-<:ᶜ q
  sound-<:ᵛ ([ p ]ₛ q)  = [ sound-≾ᵣ s p ]ₛ sound-<:ᵛ q

  sound-<:ᶜ (p ‼ₛ q) = sound-<:ᵛ p ‼ₛ sound-≾ₑ s q

  -- the var-rule disjunction

  sound-VarOK : {A : OVType Θ} {ρ : RExp Θ} → VarOK Q A ρ
              → Eternal (⟦ A ⟧ᵛ σ) ⊎ (⟦ ρ ⟧ʳ σ ≾ᵣ uᵣ)
  sound-VarOK (et-ok et) = inj₁ (sound-⊩ᴱ et)
  sound-VarOK (≾ᵘ-ok le) = inj₂ (sound-≾ᵣ s le)
  sound-VarOK (hyp-ok m p q) with ⊨disj s m
  ... | inj₁ et = inj₁ (subst Eternal (sym (sound-≡̂ᵛ σ p)) et)
  ... | inj₂ le = inj₂ (≾ᵣ-trans (sound-≾ᵣ s q) le)

------------------------------------------------------------------------
-- Memberships

⟦_⟧ˣ : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ}
     → A ∈̂[ ρ ] Γ → {σ : DInst Θ} → ⟦ A ⟧ᵛ σ ∈[ ⟦ ρ ⟧ʳ σ ] ⟦ Γ ⟧ᶜᵗˣ σ
⟦ Hd ⟧ˣ       = Hd
⟦ Tl-∷ x ⟧ˣ   = Tl-∷ ⟦ x ⟧ˣ
⟦ Tl-⟨⟩ x ⟧ˣ  = Tl-⟨⟩ ⟦ x ⟧ˣ

-- at the same position

⟦⟧ˣ-pos : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ} {σ : DInst Θ}
        → (x : A ∈̂[ ρ ] Γ) → CE.var-pos (⟦ x ⟧ˣ {σ}) ≡ toℕ (var-pos x)
⟦⟧ˣ-pos Hd        = refl
⟦⟧ˣ-pos (Tl-∷ x)  = cong suc (⟦⟧ˣ-pos x)
⟦⟧ˣ-pos (Tl-⟨⟩ x) = ⟦⟧ˣ-pos x

------------------------------------------------------------------------
-- A handler clause is typed under `wkᵉ-H Q`, which every extension of
-- an instance satisfying `Q` satisfies

⊨ᴰ-,ᵉ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} → (c : E) → σ ⊨ᴰ Q → (σ ,ᵉᴰ c) ⊨ᴰ wkᵉ-H Q
⊨ᴰ-,ᵉ {Θ} {σ} {Q} c s = mk⊨ᴰ ets' subᵥ' ordᵣ' ordₑ' disj'
  where
    ets' : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Eternal (ty (σ ,ᵉᴰ c) α)
    ets' m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | _ , m₀ , refl = ⊨ets s m₀

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → ty (σ ,ᵉᴰ c) α <:ᵛ ty (σ ,ᵉᴰ c) β
    subᵥ' m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | _ , m₀ , refl = ⊨subᵥ s m₀

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
          → ⟦ ρ ⟧ʳ (σ ,ᵉᴰ c) ≾ᵣ ⟦ ρ' ⟧ʳ (σ ,ᵉᴰ c)
    ordᵣ' m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ _≾ᵣ_ (sym (⟦wkᵉ⟧ʳ σ c ρ₀)) (sym (⟦wkᵉ⟧ʳ σ c ρ₀')) (⊨ordᵣ s m₀)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
          → ⟦ ε ⟧ᵉ (σ ,ᵉᴰ c) ≾ₑ ⟦ ε' ⟧ᵉ (σ ,ᵉᴰ c)
    ordₑ' m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ _≾ₑ_ (sym (⟦wkᵉ⟧ᵉ σ c ε₀)) (sym (⟦wkᵉ⟧ᵉ σ c ε₀')) (⊨ordₑ s m₀)

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q)
          → Eternal (⟦ A ⟧ᵛ (σ ,ᵉᴰ c)) ⊎ (⟦ ρ ⟧ʳ (σ ,ᵉᴰ c) ≾ᵣ uᵣ)
    disj' m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (λ X r → Eternal X ⊎ (r ≾ᵣ uᵣ)) (sym (⟦wkᵉ⟧ᵛ σ c A₀)) (sym (⟦wkᵉ⟧ʳ σ c ρ₀))
             (⊨disj s m₀)
