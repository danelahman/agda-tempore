-------------------------------------------------------------------
-- Shape-preserving subtyping of open value and computation types  --
--                                                                 --
-- Mirrors `Syntax.Subtyping` former by former: structural         --
-- inductive families, one constructor per pair of matching type    --
-- formers, no `refl` or `trans` constructor. The grade slots carry --
-- entailments from a hypothesis set `Q` instead of closed grade    --
-- facts, so the relation is parameterised by `Q`.                  --
--                                                                 --
-- At a type variable the relation is equality: an unknown head is  --
-- equalised by unification, never by subtyping.                    --
--                                                                 --
-- Irrelevance does not mirror, entailment being proof-relevant.    --
-------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Open.Subtyping (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

infix  4  _∣_<:̂ᵛ_ _∣_<:̂ᶜ_
infix  37 [_]ₛ_
infix  32 _|×|ₛ_
infixr 30 _⇒ₛ_
infix  31 _‼ₛ_

-- The relation

data _∣_<:̂ᵛ_ {Θ : Scope} (Q : Hyps Θ) : OVType Θ → OVType Θ → Set
data _∣_<:̂ᶜ_ {Θ : Scope} (Q : Hyps Θ) : OCType Θ → OCType Θ → Set

data _∣_<:̂ᵛ_ {Θ} Q where
  tvarₛ  : ∀ {α β} → α ≡ β → Q ∣ tvar α <:̂ᵛ tvar β
  Baseₛ  : ∀ {b b'} → b ≡ b' → Q ∣ Base b <:̂ᵛ Base b'
  Unitₛ  : Q ∣ Unit <:̂ᵛ Unit
  Boolₛ  : Q ∣ Bool <:̂ᵛ Bool
  _|×|ₛ_ : ∀ {A A' B B'} → Q ∣ A <:̂ᵛ A' → Q ∣ B <:̂ᵛ B'
         → Q ∣ (A |×| B) <:̂ᵛ (A' |×| B')
  Emptyₛ : Q ∣ Empty <:̂ᵛ Empty
  _⇒ₛ_   : ∀ {A A' C C'} → Q ∣ A' <:̂ᵛ A → Q ∣ C <:̂ᶜ C'
         → Q ∣ (A ⇒ C) <:̂ᵛ (A' ⇒ C')
  [_]ₛ_  : ∀ {ρ ρ' A A'} → Q ⊩ ρ' ≾̂ᵣ ρ → Q ∣ A <:̂ᵛ A'
         → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A')

data _∣_<:̂ᶜ_ {Θ} Q where
  _‼ₛ_ : ∀ {A A' ε ε'} → Q ∣ A <:̂ᵛ A' → Q ⊩ ε ≾̂ₑ ε'
       → Q ∣ (A ‼ ε) <:̂ᶜ (A' ‼ ε')

-- Inversion at box type

<:̂ᵛ-box-grade : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
              → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ⊩ ρ' ≾̂ᵣ ρ
<:̂ᵛ-box-grade ([ q ]ₛ _) = q

<:̂ᵛ-box-type : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
             → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ∣ A <:̂ᵛ A'
<:̂ᵛ-box-type ([ _ ]ₛ p) = p

-- Reflexivity

<:̂ᵛ-refl : ∀ {Θ} {Q : Hyps Θ} → (A : OVType Θ) → Q ∣ A <:̂ᵛ A
<:̂ᶜ-refl : ∀ {Θ} {Q : Hyps Θ} → (C : OCType Θ) → Q ∣ C <:̂ᶜ C

<:̂ᵛ-refl (tvar α)  = tvarₛ refl
<:̂ᵛ-refl (Base b)  = Baseₛ refl
<:̂ᵛ-refl Unit      = Unitₛ
<:̂ᵛ-refl Bool      = Boolₛ
<:̂ᵛ-refl (A |×| B) = <:̂ᵛ-refl A |×|ₛ <:̂ᵛ-refl B
<:̂ᵛ-refl Empty     = Emptyₛ
<:̂ᵛ-refl (A ⇒ C)   = <:̂ᵛ-refl A ⇒ₛ <:̂ᶜ-refl C
<:̂ᵛ-refl ([ ρ ] A) = [ ⊩≾̂ᵣ-refl ]ₛ <:̂ᵛ-refl A

<:̂ᶜ-refl (A ‼ ε) = <:̂ᵛ-refl A ‼ₛ ⊩≾̂ₑ-refl

-- Transitivity; the contravariant positions compose in the opposite order

<:̂ᵛ-trans : ∀ {Θ} {Q : Hyps Θ} {A B C}
          → Q ∣ A <:̂ᵛ B → Q ∣ B <:̂ᵛ C → Q ∣ A <:̂ᵛ C
<:̂ᶜ-trans : ∀ {Θ} {Q : Hyps Θ} {C₁ C₂ C₃}
          → Q ∣ C₁ <:̂ᶜ C₂ → Q ∣ C₂ <:̂ᶜ C₃ → Q ∣ C₁ <:̂ᶜ C₃

<:̂ᵛ-trans (tvarₛ p)  (tvarₛ q)  = tvarₛ (trans p q)
<:̂ᵛ-trans (Baseₛ p)  (Baseₛ q)  = Baseₛ (trans p q)
<:̂ᵛ-trans Unitₛ      Unitₛ      = Unitₛ
<:̂ᵛ-trans Boolₛ      Boolₛ      = Boolₛ
<:̂ᵛ-trans (p |×|ₛ r) (q |×|ₛ s) = <:̂ᵛ-trans p q |×|ₛ <:̂ᵛ-trans r s
<:̂ᵛ-trans Emptyₛ     Emptyₛ     = Emptyₛ
<:̂ᵛ-trans (p ⇒ₛ r)   (q ⇒ₛ s)   = <:̂ᵛ-trans q p ⇒ₛ <:̂ᶜ-trans r s
<:̂ᵛ-trans ([ p ]ₛ r) ([ q ]ₛ s) = [ transᵣ q p ]ₛ <:̂ᵛ-trans r s

<:̂ᶜ-trans (p ‼ₛ r) (q ‼ₛ s) = <:̂ᵛ-trans p q ‼ₛ transₑ r s

-- Eternality lives on the shared skeleton, so it transfers along
-- `_∣_<:̂ᵛ_` in both directions.

<:̂ᵛ-eternalˡ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → Q ⊩ᴱ B → Q ⊩ᴱ A
<:̂ᵛ-eternalˡ (tvarₛ refl) et          = et
<:̂ᵛ-eternalˡ (Baseₛ refl) et          = et
<:̂ᵛ-eternalˡ Unitₛ        et          = et
<:̂ᵛ-eternalˡ Boolₛ        et          = et
<:̂ᵛ-eternalˡ (p |×|ₛ r)   (et |×|ₑ e) = <:̂ᵛ-eternalˡ p et |×|ₑ <:̂ᵛ-eternalˡ r e
<:̂ᵛ-eternalˡ Emptyₛ       et          = et

<:̂ᵛ-eternalʳ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → Q ⊩ᴱ A → Q ⊩ᴱ B
<:̂ᵛ-eternalʳ (tvarₛ refl) et          = et
<:̂ᵛ-eternalʳ (Baseₛ refl) et          = et
<:̂ᵛ-eternalʳ Unitₛ        et          = et
<:̂ᵛ-eternalʳ Boolₛ        et          = et
<:̂ᵛ-eternalʳ (p |×|ₛ r)   (et |×|ₑ e) = <:̂ᵛ-eternalʳ p et |×|ₑ <:̂ᵛ-eternalʳ r e
<:̂ᵛ-eternalʳ Emptyₛ       et          = et

-- Stability under a scope substitution, mirroring `⊩-substᵣ`. A type
-- variable's image is an arbitrary open type, so `tvarₛ` lands on
-- reflexivity at that image.

<:̂ᵛ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A A' : OVType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ A <:̂ᵛ A' → Q' ∣ A [ σ ]ᵛ <:̂ᵛ A' [ σ ]ᵛ
<:̂ᶜ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {C C' : OCType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ C <:̂ᶜ C' → Q' ∣ C [ σ ]ᶜ <:̂ᶜ C' [ σ ]ᶜ

<:̂ᵛ-subst {σ = σ} h (tvarₛ {α} refl) = <:̂ᵛ-refl (sTy σ α)
<:̂ᵛ-subst         h (Baseₛ p)        = Baseₛ p
<:̂ᵛ-subst         h Unitₛ            = Unitₛ
<:̂ᵛ-subst         h Boolₛ            = Boolₛ
<:̂ᵛ-subst         h (p |×|ₛ r)       = <:̂ᵛ-subst h p |×|ₛ <:̂ᵛ-subst h r
<:̂ᵛ-subst         h Emptyₛ           = Emptyₛ
<:̂ᵛ-subst         h (p ⇒ₛ r)         = <:̂ᵛ-subst h p ⇒ₛ <:̂ᶜ-subst h r
<:̂ᵛ-subst         h ([ q ]ₛ p)       = [ ⊩-substᵣ h q ]ₛ <:̂ᵛ-subst h p

<:̂ᶜ-subst h (p ‼ₛ q) = <:̂ᵛ-subst h p ‼ₛ ⊩-substₑ h q

-- Stability under the scope extensions

<:̂ᵛ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵗ-H Q ∣ wkᵗ-v A <:̂ᵛ wkᵗ-v A'
<:̂ᵛ-wkᵗ {Q = Q} {A} {A'} p =
  subst₂ (wkᵗ-H Q ∣_<:̂ᵛ_) (wkˢᵗ-v A) (wkˢᵗ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵗ p)

<:̂ᵛ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkʳ-H Q ∣ wkʳ-v A <:̂ᵛ wkʳ-v A'
<:̂ᵛ-wkʳ {Q = Q} {A} {A'} p =
  subst₂ (wkʳ-H Q ∣_<:̂ᵛ_) (wkˢʳ-v A) (wkˢʳ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkʳ p)

<:̂ᵛ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵉ-H Q ∣ wkᵉ-v A <:̂ᵛ wkᵉ-v A'
<:̂ᵛ-wkᵉ {Q = Q} {A} {A'} p =
  subst₂ (wkᵉ-H Q ∣_<:̂ᵛ_) (wkˢᵉ-v A) (wkˢᵉ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵉ p)
