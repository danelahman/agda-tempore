-------------------------------------------------------------------
-- Shape-preserving subtyping of value and computation types      --
--                                                                --
-- Structural inductive families: one constructor per pair of     --
-- matching type formers, and no `refl` or `trans` constructor,   --
-- so reflexivity, transitivity and proof irrelevance are lemmas  --
-- and mismatched shapes are uninhabited.                         --
--                                                                --
-- A function's domain and a box's grade are contravariant, a     --
-- computation's effect covariant. The box direction agrees with  --
-- `unbox`'s premise: a larger box grade is the weaker obligation. --
-------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Subtyping (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S

infix  4  _<:ᵛ_ _<:ᶜ_
infix  37 [_]ₛ_
infix  32 _|×|ₛ_
infixr 30 _⇒ₛ_
infix  31 _‼ₛ_

-- The relation

data _<:ᵛ_ : VType → VType → Set
data _<:ᶜ_ : CType → CType → Set

data _<:ᵛ_ where
  Baseₛ  : ∀ {b b'} → b ≡ b' → Base b <:ᵛ Base b'
  Unitₛ  : Unit <:ᵛ Unit
  Boolₛ  : Bool <:ᵛ Bool
  _|×|ₛ_ : ∀ {A A' B B'} → A <:ᵛ A' → B <:ᵛ B' → (A |×| B) <:ᵛ (A' |×| B')
  Emptyₛ : Empty <:ᵛ Empty
  _⇒ₛ_   : ∀ {A A' C C'} → A' <:ᵛ A → C <:ᶜ C' → (A ⇒ C) <:ᵛ (A' ⇒ C')
  [_]ₛ_  : ∀ {ρ ρ' A A'} → ρ' ≾ᵣ ρ → A <:ᵛ A' → ([ ρ ] A) <:ᵛ ([ ρ' ] A')

data _<:ᶜ_ where
  _‼ₛ_ : ∀ {A A' ε ε'} → A <:ᵛ A' → ε ≾ₑ ε' → (A ‼ ε) <:ᶜ (A' ‼ ε')

-- Inversion at box type, for the sites that hold a witness they cannot
-- match on because its endpoints are neutral.

<:ᵛ-box-grade : ∀ {ρ ρ' A A'} → ([ ρ ] A) <:ᵛ ([ ρ' ] A') → ρ' ≾ᵣ ρ
<:ᵛ-box-grade ([ q ]ₛ _) = q

<:ᵛ-box-type : ∀ {ρ ρ' A A'} → ([ ρ ] A) <:ᵛ ([ ρ' ] A') → A <:ᵛ A'
<:ᵛ-box-type ([ _ ]ₛ p) = p

-- Reflexivity

<:ᵛ-refl : (A : VType) → A <:ᵛ A
<:ᶜ-refl : (C : CType) → C <:ᶜ C

<:ᵛ-refl (Base b)  = Baseₛ refl
<:ᵛ-refl Unit      = Unitₛ
<:ᵛ-refl Bool      = Boolₛ
<:ᵛ-refl (A |×| B) = <:ᵛ-refl A |×|ₛ <:ᵛ-refl B
<:ᵛ-refl Empty     = Emptyₛ
<:ᵛ-refl (A ⇒ C)   = <:ᵛ-refl A ⇒ₛ <:ᶜ-refl C
<:ᵛ-refl ([ ρ ] A) = [ ≾ᵣ-refl ]ₛ <:ᵛ-refl A

<:ᶜ-refl (A ‼ ε) = <:ᵛ-refl A ‼ₛ ≾ₑ-refl

-- Transitivity; the contravariant positions compose in the opposite order

<:ᵛ-trans : ∀ {A B C} → A <:ᵛ B → B <:ᵛ C → A <:ᵛ C
<:ᶜ-trans : ∀ {C₁ C₂ C₃} → C₁ <:ᶜ C₂ → C₂ <:ᶜ C₃ → C₁ <:ᶜ C₃

<:ᵛ-trans (Baseₛ p)  (Baseₛ q)  = Baseₛ (trans p q)
<:ᵛ-trans Unitₛ      Unitₛ      = Unitₛ
<:ᵛ-trans Boolₛ      Boolₛ      = Boolₛ
<:ᵛ-trans (p |×|ₛ r) (q |×|ₛ s) = <:ᵛ-trans p q |×|ₛ <:ᵛ-trans r s
<:ᵛ-trans Emptyₛ     Emptyₛ     = Emptyₛ
<:ᵛ-trans (p ⇒ₛ r)   (q ⇒ₛ s)   = <:ᵛ-trans q p ⇒ₛ <:ᶜ-trans r s
<:ᵛ-trans ([ p ]ₛ r) ([ q ]ₛ s) = [ ≾ᵣ-trans q p ]ₛ <:ᵛ-trans r s

<:ᶜ-trans (p ‼ₛ r) (q ‼ₛ s) = <:ᵛ-trans p q ‼ₛ ≾ₑ-trans r s

-- Subtyping is a *property* of a pair of types: any two witnesses
-- coincide, by irrelevance of the grade orderings and UIP at `Base`.

<:ᵛ-irrelevant : ∀ {A B} → (p q : A <:ᵛ B) → p ≡ q
<:ᶜ-irrelevant : ∀ {C₁ C₂} → (p q : C₁ <:ᶜ C₂) → p ≡ q

<:ᵛ-irrelevant (Baseₛ p)  (Baseₛ q)  = cong Baseₛ uip
<:ᵛ-irrelevant Unitₛ      Unitₛ      = refl
<:ᵛ-irrelevant Boolₛ      Boolₛ      = refl
<:ᵛ-irrelevant (p |×|ₛ r) (q |×|ₛ s) =
  cong₂ _|×|ₛ_ (<:ᵛ-irrelevant p q) (<:ᵛ-irrelevant r s)
<:ᵛ-irrelevant Emptyₛ     Emptyₛ     = refl
<:ᵛ-irrelevant (p ⇒ₛ r)   (q ⇒ₛ s)   =
  cong₂ _⇒ₛ_ (<:ᵛ-irrelevant p q) (<:ᶜ-irrelevant r s)
<:ᵛ-irrelevant ([ p ]ₛ r) ([ q ]ₛ s) =
  cong₂ [_]ₛ_ (≾ᵣ-irrelevant p q) (<:ᵛ-irrelevant r s)

<:ᶜ-irrelevant (p ‼ₛ r) (q ‼ₛ s) =
  cong₂ _‼ₛ_ (<:ᵛ-irrelevant p q) (≾ₑ-irrelevant r s)

-- Eternality lives on the shared skeleton — `Eternal` has no `_⇒_` and
-- no `[_]_` clause, and the only grade it could see is a box's — so it
-- transfers along `_<:ᵛ_` in both directions.

<:ᵛ-eternalˡ : ∀ {A B} → A <:ᵛ B → Eternal B → Eternal A
<:ᵛ-eternalˡ (Baseₛ refl) et          = et
<:ᵛ-eternalˡ Unitₛ        et          = et
<:ᵛ-eternalˡ Boolₛ        et          = et
<:ᵛ-eternalˡ (p |×|ₛ r)   (et |×|ₑ e) = <:ᵛ-eternalˡ p et |×|ₑ <:ᵛ-eternalˡ r e
<:ᵛ-eternalˡ Emptyₛ       et          = et

<:ᵛ-eternalʳ : ∀ {A B} → A <:ᵛ B → Eternal A → Eternal B
<:ᵛ-eternalʳ (Baseₛ refl) et          = et
<:ᵛ-eternalʳ Unitₛ        et          = et
<:ᵛ-eternalʳ Boolₛ        et          = et
<:ᵛ-eternalʳ (p |×|ₛ r)   (et |×|ₑ e) = <:ᵛ-eternalʳ p et |×|ₑ <:ᵛ-eternalʳ r e
<:ᵛ-eternalʳ Emptyₛ       et          = et
