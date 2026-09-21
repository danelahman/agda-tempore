------------------------------------------------------------------
-- Hypotheses and entailment of the mirrored language             --
--                                                                --
-- A hypothesis set `Hyps Θ` collects the eternality atoms on     --
-- type variables, the assumed subtyping atoms between type       --
-- variables, the assumed orderings between open grade            --
-- expressions, and the assumed var-rule disjunctions, under      --
-- which a mirrored typing derivation is built. Entailment        --
-- (`_⊩ᵗᵛ_≾_`, `_⊩_≾̂ᵣ_`, `_⊩_≾̂ₑ_`, `_⊩ᴱ_`, `_∣_<:̂ᵛ_`, `VarOK`)   --
-- is an inductive under-approximation of truth in all            --
-- groundings.                                                    --
--                                                                --
-- Open subtyping is defined here too, with its inversion and     --
-- stability lemmas: `_⊩ᴴ_[_]` already mentions the relation.     --
--                                                                --
-- Judgements under such a set are HM(X)'s constrained types      --
-- (Odersky, Sulzmann, Wehr 1999) and Jones's qualified types     --
-- (1994); the set plays the role of OutsideIn(X)'s given         --
-- constraints (Vytiniotis et al., JFP 2011).                     --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Hyps (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- Only the eternal-base-type predicate is needed; the constructors of the
-- closed `Eternal` are mirrored below and would otherwise clash.

open import Syntax.Types S using (EternalBaseType)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S

-- Hypothesis sets

record Hyps (Θ : Scope) : Set where
  constructor hyps
  field
    ets  : List (TyVar Θ)                     -- eternality atoms on type variables
    subᵥ : List (TyVar Θ × TyVar Θ)           -- assumed subtyping between type variables
    ordᵣ : List (RExp Θ × RExp Θ)             -- assumed resource-grade orderings
    ordₑ : List (EExp Θ × EExp Θ)             -- assumed effect-grade orderings
    disj : List (OVType Θ × RExp Θ)           -- assumed var-rule disjunctions

open Hyps public

-- Empty hypothesis set

∅ᴴ : ∀ {Θ} → Hyps Θ
∅ᴴ = hyps [] [] [] [] []

-- Pairwise action of a function on a homogeneous pair

mapᵖ : ∀ {A B : Set} → (A → B) → A × A → B × B
mapᵖ f (x , y) = f x , f y

-- Componentwise action on a type-and-grade pair

mapᵈ : ∀ {Θ Θ'} → (OVType Θ → OVType Θ') → (RExp Θ → RExp Θ')
     → OVType Θ × RExp Θ → OVType Θ' × RExp Θ'
mapᵈ f g (A , ρ) = f A , g ρ

-- Action of the scope extensions on hypothesis sets

wkᵗ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +ty)
wkᵗ-H {Θ} Q = hyps (map (wkᵗ-tv Θ) (ets Q))
                   (map (mapᵖ (wkᵗ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkᵗ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵗ-e) (ordₑ Q))
                   (map (mapᵈ wkᵗ-v wkᵗ-r) (disj Q))

wkʳ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +r)
wkʳ-H {Θ} Q = hyps (map (wkʳ-tv Θ) (ets Q))
                   (map (mapᵖ (wkʳ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkʳ-r) (ordᵣ Q))
                   (map (mapᵖ wkʳ-e) (ordₑ Q))
                   (map (mapᵈ wkʳ-v wkʳ-r) (disj Q))

wkᵉ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +e)
wkᵉ-H {Θ} Q = hyps (map (wkᵉ-tv Θ) (ets Q))
                   (map (mapᵖ (wkᵉ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkᵉ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵉ-e) (ordₑ Q))
                   (map (mapᵈ wkᵉ-v wkᵉ-r) (disj Q))

-- Assumed subtyping between type variables, closed under reflexivity
-- and transitivity

infix 4 _⊩ᵗᵛ_≾_

data _⊩ᵗᵛ_≾_ {Θ : Scope} (Q : Hyps Θ) : TyVar Θ → TyVar Θ → Set where
  reflᵗᵛ  : ∀ {α} → Q ⊩ᵗᵛ α ≾ α
  hypᵗᵛ   : ∀ {α β} → (α , β) ∈ subᵥ Q → Q ⊩ᵗᵛ α ≾ β
  transᵗᵛ : ∀ {α β γ} → Q ⊩ᵗᵛ α ≾ β → Q ⊩ᵗᵛ β ≾ γ → Q ⊩ᵗᵛ α ≾ γ

-- The monoid laws, the constants' arithmetic, and `∣_∣̂ᵉ` being a monoid
-- morphism; no hypotheses involved.

infix 4 _≡̂ᵣ_ _≡̂ₑ_

data _≡̂ᵣ_ {Θ : Scope} : RExp Θ → RExp Θ → Set
data _≡̂ₑ_ {Θ : Scope} : EExp Θ → EExp Θ → Set

data _≡̂ᵣ_ {Θ} where
  ≡̂ᵣ-refl      : ∀ {ρ} → ρ ≡̂ᵣ ρ
  ≡̂ᵣ-sym       : ∀ {ρ ρ'} → ρ ≡̂ᵣ ρ' → ρ' ≡̂ᵣ ρ
  ≡̂ᵣ-trans     : ∀ {ρ ρ' ρ''} → ρ ≡̂ᵣ ρ' → ρ' ≡̂ᵣ ρ'' → ρ ≡̂ᵣ ρ''
  ≡̂ᵣ-cong      : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≡̂ᵣ ρ₁' → ρ₂ ≡̂ᵣ ρ₂'
               → ρ₁ ·̂ᵣ ρ₂ ≡̂ᵣ ρ₁' ·̂ᵣ ρ₂'
  ≡̂ᵣ-assoc     : ∀ {ρ₁ ρ₂ ρ₃} → (ρ₁ ·̂ᵣ ρ₂) ·̂ᵣ ρ₃ ≡̂ᵣ ρ₁ ·̂ᵣ (ρ₂ ·̂ᵣ ρ₃)
  ≡̂ᵣ-identityˡ : ∀ {ρ} → ûᵣ ·̂ᵣ ρ ≡̂ᵣ ρ
  ≡̂ᵣ-identityʳ : ∀ {ρ} → ρ ·̂ᵣ ûᵣ ≡̂ᵣ ρ
  ≡̂ᵣ-const-·   : ∀ {ρ ρ'} → rconst ρ ·̂ᵣ rconst ρ' ≡̂ᵣ rconst (ρ ·ᵣ ρ')
  ≡̂ᵣ-map-·     : ∀ {ε ε'} → ∣ ε ·̂ₑ ε' ∣̂ᵉ ≡̂ᵣ ∣ ε ∣̂ᵉ ·̂ᵣ ∣ ε' ∣̂ᵉ
  ≡̂ᵣ-map-const : ∀ {e} → ∣ econst e ∣̂ᵉ ≡̂ᵣ rconst (mapᵉ e)
  ≡̂ᵣ-map-cong  : ∀ {ε ε'} → ε ≡̂ₑ ε' → ∣ ε ∣̂ᵉ ≡̂ᵣ ∣ ε' ∣̂ᵉ

data _≡̂ₑ_ {Θ} where
  ≡̂ₑ-refl      : ∀ {ε} → ε ≡̂ₑ ε
  ≡̂ₑ-sym       : ∀ {ε ε'} → ε ≡̂ₑ ε' → ε' ≡̂ₑ ε
  ≡̂ₑ-trans     : ∀ {ε ε' ε''} → ε ≡̂ₑ ε' → ε' ≡̂ₑ ε'' → ε ≡̂ₑ ε''
  ≡̂ₑ-cong      : ∀ {ε₁ ε₁' ε₂ ε₂'} → ε₁ ≡̂ₑ ε₁' → ε₂ ≡̂ₑ ε₂'
               → ε₁ ·̂ₑ ε₂ ≡̂ₑ ε₁' ·̂ₑ ε₂'
  ≡̂ₑ-assoc     : ∀ {ε₁ ε₂ ε₃} → (ε₁ ·̂ₑ ε₂) ·̂ₑ ε₃ ≡̂ₑ ε₁ ·̂ₑ (ε₂ ·̂ₑ ε₃)
  ≡̂ₑ-identityˡ : ∀ {ε} → ûₑ ·̂ₑ ε ≡̂ₑ ε
  ≡̂ₑ-identityʳ : ∀ {ε} → ε ·̂ₑ ûₑ ≡̂ₑ ε
  ≡̂ₑ-const-·   : ∀ {ε ε'} → econst ε ·̂ₑ econst ε' ≡̂ₑ econst (ε ·ₑ ε')

infix 4 _⊩_≾̂ᵣ_ _⊩_≾̂ₑ_

-- Unit-minimality of a grade monoid, as a property of the closed grades

UnitMinᵣ : Set
UnitMinᵣ = (ρ₀ : R) → uᵣ ≾ᵣ ρ₀

UnitMinₑ : Set
UnitMinₑ = (ε₀ : E) → uₑ ≾ₑ ε₀

data _⊩_≾̂ᵣ_ {Θ : Scope} (Q : Hyps Θ) : RExp Θ → RExp Θ → Set
data _⊩_≾̂ₑ_ {Θ : Scope} (Q : Hyps Θ) : EExp Θ → EExp Θ → Set

data _⊩_≾̂ᵣ_ {Θ} Q where
  hypᵣ     : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q ⊩ ρ ≾̂ᵣ ρ'
  atomᵣ    : ∀ {ρ ρ'} → ρ ≾ᵣ ρ' → Q ⊩ rconst ρ ≾̂ᵣ rconst ρ'
  eqᵣ      : ∀ {ρ ρ'} → ρ ≡̂ᵣ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
  transᵣ   : ∀ {ρ ρ' ρ''} → Q ⊩ ρ ≾̂ᵣ ρ' → Q ⊩ ρ' ≾̂ᵣ ρ'' → Q ⊩ ρ ≾̂ᵣ ρ''
  monoᵣ    : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → Q ⊩ ρ₁ ≾̂ᵣ ρ₁' → Q ⊩ ρ₂ ≾̂ᵣ ρ₂'
           → Q ⊩ ρ₁ ·̂ᵣ ρ₂ ≾̂ᵣ ρ₁' ·̂ᵣ ρ₂'
  map-mono : ∀ {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ∣ ε ∣̂ᵉ ≾̂ᵣ ∣ ε' ∣̂ᵉ
  -- optional unit-minimality; the premise is the property of the grade monoid
  minᵣ     : ∀ {ρ} → UnitMinᵣ → Q ⊩ ûᵣ ≾̂ᵣ ρ

data _⊩_≾̂ₑ_ {Θ} Q where
  hypₑ   : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q ⊩ ε ≾̂ₑ ε'
  atomₑ  : ∀ {ε ε'} → ε ≾ₑ ε' → Q ⊩ econst ε ≾̂ₑ econst ε'
  eqₑ    : ∀ {ε ε'} → ε ≡̂ₑ ε' → Q ⊩ ε ≾̂ₑ ε'
  transₑ : ∀ {ε ε' ε''} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ε' ≾̂ₑ ε'' → Q ⊩ ε ≾̂ₑ ε''
  monoₑ  : ∀ {ε₁ ε₁' ε₂ ε₂'} → Q ⊩ ε₁ ≾̂ₑ ε₁' → Q ⊩ ε₂ ≾̂ₑ ε₂'
         → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ ε₁' ·̂ₑ ε₂'
  -- optional unit-minimality; the premise is the property of the grade monoid
  minₑ   : ∀ {ε} → UnitMinₑ → Q ⊩ ûₑ ≾̂ₑ ε

-- Entailed ordering is reflexive

⊩≾̂ᵣ-refl : ∀ {Θ} {Q : Hyps Θ} {ρ} → Q ⊩ ρ ≾̂ᵣ ρ
⊩≾̂ᵣ-refl = eqᵣ ≡̂ᵣ-refl

⊩≾̂ₑ-refl : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ≾̂ₑ ε
⊩≾̂ₑ-refl = eqₑ ≡̂ₑ-refl

-- Mirrors `Eternal` of `Syntax.Types`, plus rules for the eternality
-- atoms of the hypothesis set and for transfer along an assumed
-- subtyping in both directions; as in the original, no rule for `_⇒_`
-- and `[_]_`.

infix 4 _⊩ᴱ_

data _⊩ᴱ_ {Θ : Scope} (Q : Hyps Θ) : OVType Θ → Set where
  et-hyp  : ∀ {α} → α ∈ ets Q → Q ⊩ᴱ tvar α
  et-subˡ : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → Q ⊩ᴱ tvar β → Q ⊩ᴱ tvar α
  et-subʳ : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → Q ⊩ᴱ tvar α → Q ⊩ᴱ tvar β
  Baseₑ   : ∀ {b} → .(EternalBaseType b) → Q ⊩ᴱ Base b
  Unitₑ   : Q ⊩ᴱ Unit
  Boolₑ   : Q ⊩ᴱ Bool
  _|×|ₑ_  : ∀ {A₁ A₂} → Q ⊩ᴱ A₁ → Q ⊩ᴱ A₂ → Q ⊩ᴱ A₁ |×| A₂
  Emptyₑ  : Q ⊩ᴱ Empty

-- The side condition of the `var` rule: `Eternal` is undecided at open
-- types, so the original's `¬ Eternal A → ρ ≾ᵣ uᵣ` becomes a disjunction,
-- met by eternality, by the ordering, or by a `disj` hypothesis.

data VarOK {Θ : Scope} (Q : Hyps Θ) (A : OVType Θ) (ρ : RExp Θ) : Set where
  et-ok  : Q ⊩ᴱ A → VarOK Q A ρ
  ≾ᵘ-ok  : Q ⊩ ρ ≾̂ᵣ ûᵣ → VarOK Q A ρ
  hyp-ok : (A , ρ) ∈ disj Q → VarOK Q A ρ

-- Shape-preserving subtyping of open value and computation types,
-- mirroring `Syntax.Subtyping` former by former: one constructor per
-- pair of matching type formers, no `refl` or `trans` constructor. The
-- grade slots carry entailments from `Q`, and an unknown head is
-- related only by an assumed subtyping.
--
-- Irrelevance does not mirror, entailment being proof-relevant.

infix  4  _∣_<:̂ᵛ_ _∣_<:̂ᶜ_
infix  37 [_]ₛ_
infix  32 _|×|ₛ_
infixr 30 _⇒ₛ_
infix  31 _‼ₛ_

data _∣_<:̂ᵛ_ {Θ : Scope} (Q : Hyps Θ) : OVType Θ → OVType Θ → Set
data _∣_<:̂ᶜ_ {Θ : Scope} (Q : Hyps Θ) : OCType Θ → OCType Θ → Set

data _∣_<:̂ᵛ_ {Θ} Q where
  tvarₛ  : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → Q ∣ tvar α <:̂ᵛ tvar β
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

-- Reflexivity

<:̂ᵛ-refl : ∀ {Θ} {Q : Hyps Θ} → (A : OVType Θ) → Q ∣ A <:̂ᵛ A
<:̂ᶜ-refl : ∀ {Θ} {Q : Hyps Θ} → (C : OCType Θ) → Q ∣ C <:̂ᶜ C

<:̂ᵛ-refl (tvar α)  = tvarₛ reflᵗᵛ
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

<:̂ᵛ-trans (tvarₛ p)  (tvarₛ q)  = tvarₛ (transᵗᵛ p q)
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
<:̂ᵛ-eternalˡ (tvarₛ p)    et          = et-subˡ p et
<:̂ᵛ-eternalˡ (Baseₛ refl) et          = et
<:̂ᵛ-eternalˡ Unitₛ        et          = et
<:̂ᵛ-eternalˡ Boolₛ        et          = et
<:̂ᵛ-eternalˡ (p |×|ₛ r)   (et |×|ₑ e) = <:̂ᵛ-eternalˡ p et |×|ₑ <:̂ᵛ-eternalˡ r e
<:̂ᵛ-eternalˡ Emptyₛ       et          = et

<:̂ᵛ-eternalʳ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → Q ⊩ᴱ A → Q ⊩ᴱ B
<:̂ᵛ-eternalʳ (tvarₛ p)    et          = et-subʳ p et
<:̂ᵛ-eternalʳ (Baseₛ refl) et          = et
<:̂ᵛ-eternalʳ Unitₛ        et          = et
<:̂ᵛ-eternalʳ Boolₛ        et          = et
<:̂ᵛ-eternalʳ (p |×|ₛ r)   (et |×|ₑ e) = <:̂ᵛ-eternalʳ p et |×|ₑ <:̂ᵛ-eternalʳ r e
<:̂ᵛ-eternalʳ Emptyₛ       et          = et

-- Inversion at the formers with no proper supertype

<:̂ᵛ-Baseˡ : ∀ {Θ} {Q : Hyps Θ} {b A} → Q ∣ Base b <:̂ᵛ A → A ≡ Base b
<:̂ᵛ-Baseˡ (Baseₛ refl) = refl

<:̂ᵛ-Unitˡ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ∣ Unit <:̂ᵛ A → A ≡ Unit
<:̂ᵛ-Unitˡ Unitₛ = refl

<:̂ᵛ-Boolˡ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ∣ Bool <:̂ᵛ A → A ≡ Bool
<:̂ᵛ-Boolˡ Boolₛ = refl

-- Inversion at a product: a supertype is a product, componentwise

<:̂ᵛ-×ˡ : ∀ {Θ} {Q : Hyps Θ} {A₁ A₂ B}
       → Q ∣ A₁ |×| A₂ <:̂ᵛ B
       → Σ[ B₁ ∈ OVType Θ ] Σ[ B₂ ∈ OVType Θ ]
           (B ≡ B₁ |×| B₂) × (Q ∣ A₁ <:̂ᵛ B₁) × (Q ∣ A₂ <:̂ᵛ B₂)
<:̂ᵛ-×ˡ (p |×|ₛ q) = _ , _ , refl , p , q

-- Inversion at box type

<:̂ᵛ-box-grade : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
              → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ⊩ ρ' ≾̂ᵣ ρ
<:̂ᵛ-box-grade ([ q ]ₛ _) = q

<:̂ᵛ-box-type : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
             → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ∣ A <:̂ᵛ A'
<:̂ᵛ-box-type ([ _ ]ₛ p) = p

-- `Q' ⊩ᴴ Q [ σ ]` says `Q'` entails every hypothesis of `Q` transported
-- along `σ`; there is no syntactic action of a substitution on `Hyps`,
-- as `ets` and `subᵥ` hold variables, whose images under `σ` are open
-- types.

infix 4 _⊩ᴴ_[_] _⊩ᴴ_

record _⊩ᴴ_[_] {Θ Θ' : Scope} (Q' : Hyps Θ') (Q : Hyps Θ) (σ : Subst Θ Θ') : Set where
  constructor mk⊩ᴴ
  field
    ⊩ets  : ∀ {α} → α ∈ ets Q → Q' ⊩ᴱ sTy σ α
    ⊩subᵥ : ∀ {α β} → (α , β) ∈ subᵥ Q → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
    ⊩ordᵣ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
    ⊩ordₑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
    ⊩disj : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)

open _⊩ᴴ_[_] public

-- Entailment between hypothesis sets over the same scope

_⊩ᴴ_ : ∀ {Θ} → Hyps Θ → Hyps Θ → Set
Q' ⊩ᴴ Q = Q' ⊩ᴴ Q [ idˢ ]

≡̂ᵣ-subst : ∀ {Θ Θ'} {ρ ρ' : RExp Θ} → (σ : Subst Θ Θ')
         → ρ ≡̂ᵣ ρ' → ρ [ σ ]ʳ ≡̂ᵣ ρ' [ σ ]ʳ
≡̂ₑ-subst : ∀ {Θ Θ'} {ε ε' : EExp Θ} → (σ : Subst Θ Θ')
         → ε ≡̂ₑ ε' → ε [ σ ]ᵉ ≡̂ₑ ε' [ σ ]ᵉ

≡̂ᵣ-subst σ ≡̂ᵣ-refl         = ≡̂ᵣ-refl
≡̂ᵣ-subst σ (≡̂ᵣ-sym p)      = ≡̂ᵣ-sym (≡̂ᵣ-subst σ p)
≡̂ᵣ-subst σ (≡̂ᵣ-trans p q)  = ≡̂ᵣ-trans (≡̂ᵣ-subst σ p) (≡̂ᵣ-subst σ q)
≡̂ᵣ-subst σ (≡̂ᵣ-cong p q)   = ≡̂ᵣ-cong (≡̂ᵣ-subst σ p) (≡̂ᵣ-subst σ q)
≡̂ᵣ-subst σ ≡̂ᵣ-assoc        = ≡̂ᵣ-assoc
≡̂ᵣ-subst σ ≡̂ᵣ-identityˡ    = ≡̂ᵣ-identityˡ
≡̂ᵣ-subst σ ≡̂ᵣ-identityʳ    = ≡̂ᵣ-identityʳ
≡̂ᵣ-subst σ ≡̂ᵣ-const-·      = ≡̂ᵣ-const-·
≡̂ᵣ-subst σ ≡̂ᵣ-map-·        = ≡̂ᵣ-map-·
≡̂ᵣ-subst σ ≡̂ᵣ-map-const    = ≡̂ᵣ-map-const
≡̂ᵣ-subst σ (≡̂ᵣ-map-cong p) = ≡̂ᵣ-map-cong (≡̂ₑ-subst σ p)

≡̂ₑ-subst σ ≡̂ₑ-refl        = ≡̂ₑ-refl
≡̂ₑ-subst σ (≡̂ₑ-sym p)     = ≡̂ₑ-sym (≡̂ₑ-subst σ p)
≡̂ₑ-subst σ (≡̂ₑ-trans p q) = ≡̂ₑ-trans (≡̂ₑ-subst σ p) (≡̂ₑ-subst σ q)
≡̂ₑ-subst σ (≡̂ₑ-cong p q)  = ≡̂ₑ-cong (≡̂ₑ-subst σ p) (≡̂ₑ-subst σ q)
≡̂ₑ-subst σ ≡̂ₑ-assoc       = ≡̂ₑ-assoc
≡̂ₑ-subst σ ≡̂ₑ-identityˡ   = ≡̂ₑ-identityˡ
≡̂ₑ-subst σ ≡̂ₑ-identityʳ   = ≡̂ₑ-identityʳ
≡̂ₑ-subst σ ≡̂ₑ-const-·     = ≡̂ₑ-const-·

⊩-substᵣ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ρ ρ' : RExp Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ ρ ≾̂ᵣ ρ' → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
⊩-substₑ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ε ε' : EExp Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ ε ≾̂ₑ ε' → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ

⊩-substᵣ            h (hypᵣ m)     = ⊩ordᵣ h m
⊩-substᵣ            h (atomᵣ p)    = atomᵣ p
⊩-substᵣ {σ = σ}    h (eqᵣ p)      = eqᵣ (≡̂ᵣ-subst σ p)
⊩-substᵣ            h (transᵣ p q) = transᵣ (⊩-substᵣ h p) (⊩-substᵣ h q)
⊩-substᵣ            h (monoᵣ p q)  = monoᵣ (⊩-substᵣ h p) (⊩-substᵣ h q)
⊩-substᵣ            h (map-mono p) = map-mono (⊩-substₑ h p)
⊩-substᵣ            h (minᵣ p)     = minᵣ p

⊩-substₑ         h (hypₑ m)     = ⊩ordₑ h m
⊩-substₑ         h (atomₑ p)    = atomₑ p
⊩-substₑ {σ = σ} h (eqₑ p)      = eqₑ (≡̂ₑ-subst σ p)
⊩-substₑ         h (transₑ p q) = transₑ (⊩-substₑ h p) (⊩-substₑ h q)
⊩-substₑ         h (monoₑ p q)  = monoₑ (⊩-substₑ h p) (⊩-substₑ h q)
⊩-substₑ         h (minₑ p)     = minₑ p

-- A type variable's image is an arbitrary open type, so an assumed
-- subtyping transports to a subtyping derivation at those images.

⊩ᵗᵛ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {α β}
          → Q' ⊩ᴴ Q [ σ ] → Q ⊩ᵗᵛ α ≾ β → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
⊩ᵗᵛ-subst {σ = σ} h (reflᵗᵛ {α})  = <:̂ᵛ-refl (sTy σ α)
⊩ᵗᵛ-subst         h (hypᵗᵛ m)     = ⊩subᵥ h m
⊩ᵗᵛ-subst         h (transᵗᵛ p q) = <:̂ᵛ-trans (⊩ᵗᵛ-subst h p) (⊩ᵗᵛ-subst h q)

⊩ᴱ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A : OVType Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ᴱ A → Q' ⊩ᴱ A [ σ ]ᵛ
⊩ᴱ-subst h (et-hyp m)     = ⊩ets h m
⊩ᴱ-subst h (et-subˡ p et) = <:̂ᵛ-eternalˡ (⊩ᵗᵛ-subst h p) (⊩ᴱ-subst h et)
⊩ᴱ-subst h (et-subʳ p et) = <:̂ᵛ-eternalʳ (⊩ᵗᵛ-subst h p) (⊩ᴱ-subst h et)
⊩ᴱ-subst h (Baseₑ p)      = Baseₑ p
⊩ᴱ-subst h Unitₑ          = Unitₑ
⊩ᴱ-subst h Boolₑ          = Boolₑ
⊩ᴱ-subst h (et₁ |×|ₑ et₂) = ⊩ᴱ-subst h et₁ |×|ₑ ⊩ᴱ-subst h et₂
⊩ᴱ-subst h Emptyₑ         = Emptyₑ

VarOK-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
                {A : OVType Θ} {ρ : RExp Θ}
            → Q' ⊩ᴴ Q [ σ ] → VarOK Q A ρ → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
VarOK-subst h (et-ok et)  = et-ok (⊩ᴱ-subst h et)
VarOK-subst h (≾ᵘ-ok le)  = ≾ᵘ-ok (⊩-substᵣ h le)
VarOK-subst h (hyp-ok m)  = ⊩disj h m

<:̂ᵛ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A A' : OVType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ A <:̂ᵛ A' → Q' ∣ A [ σ ]ᵛ <:̂ᵛ A' [ σ ]ᵛ
<:̂ᶜ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {C C' : OCType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ C <:̂ᶜ C' → Q' ∣ C [ σ ]ᶜ <:̂ᶜ C' [ σ ]ᶜ

<:̂ᵛ-subst h (tvarₛ p)  = ⊩ᵗᵛ-subst h p
<:̂ᵛ-subst h (Baseₛ p)  = Baseₛ p
<:̂ᵛ-subst h Unitₛ      = Unitₛ
<:̂ᵛ-subst h Boolₛ      = Boolₛ
<:̂ᵛ-subst h (p |×|ₛ r) = <:̂ᵛ-subst h p |×|ₛ <:̂ᵛ-subst h r
<:̂ᵛ-subst h Emptyₛ     = Emptyₛ
<:̂ᵛ-subst h (p ⇒ₛ r)   = <:̂ᵛ-subst h p ⇒ₛ <:̂ᶜ-subst h r
<:̂ᵛ-subst h ([ q ]ₛ p) = [ ⊩-substᵣ h q ]ₛ <:̂ᵛ-subst h p

<:̂ᶜ-subst h (p ‼ₛ q) = <:̂ᵛ-subst h p ‼ₛ ⊩-substₑ h q

⊩ᴴ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ᴴ Q [ idˢ ]
⊩ᴴ-refl {Q = Q} =
  mk⊩ᴴ et-hyp
       (λ m → tvarₛ (hypᵗᵛ m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ')) (hypᵣ m))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε')) (hypₑ m))
       (λ {A} {ρ} m →
          subst₂ (VarOK Q) (sym ([id]ᵛ A)) (sym ([id]ʳ ρ)) (hyp-ok m))

⊩ᴴ-⨟ : ∀ {Θ Θ' Θ''} {Q : Hyps Θ} {Q' : Hyps Θ'} {Q'' : Hyps Θ''}
       {σ : Subst Θ Θ'} {δ : Subst Θ' Θ''}
     → Q'' ⊩ᴴ Q' [ δ ] → Q' ⊩ᴴ Q [ σ ] → Q'' ⊩ᴴ Q [ σ ⨟ˢ δ ]
⊩ᴴ-⨟ {Q'' = Q''} {σ = σ} {δ = δ} h' h =
  mk⊩ᴴ (λ m → ⊩ᴱ-subst h' (⊩ets h m))
       (λ m → <:̂ᵛ-subst h' (⊩subᵥ h m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q'' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
                 (⊩-substᵣ h' (⊩ordᵣ h m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q'' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)
                 (⊩-substₑ h' (⊩ordₑ h m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK Q'') ([⨟]ᵛ A σ δ) ([⨟]ʳ ρ σ δ)
                 (VarOK-subst h' (⊩disj h m)))

-- Weakening a hypothesis set is the action of the weakening substitution,
-- so entailment is stable under it.

⊩ᴴ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} → wkᵗ-H Q ⊩ᴴ Q [ wkˢᵗ ]
⊩ᴴ-wkᵗ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkᵗ-tv Θ) m))
       (λ m → tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (wkᵗ-tv Θ)) m)))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢᵗ-r ρ)) (sym (wkˢᵗ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkᵗ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢᵗ-e ε)) (sym (wkˢᵗ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkᵗ-e) m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK (wkᵗ-H Q)) (sym (wkˢᵗ-v A)) (sym (wkˢᵗ-r ρ))
                 (hyp-ok (∈-map⁺ (mapᵈ wkᵗ-v wkᵗ-r) m)))

⊩ᴴ-wkʳ : ∀ {Θ} {Q : Hyps Θ} → wkʳ-H Q ⊩ᴴ Q [ wkˢʳ ]
⊩ᴴ-wkʳ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkʳ-tv Θ) m))
       (λ m → tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (wkʳ-tv Θ)) m)))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢʳ-r ρ)) (sym (wkˢʳ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkʳ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢʳ-e ε)) (sym (wkˢʳ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkʳ-e) m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK (wkʳ-H Q)) (sym (wkˢʳ-v A)) (sym (wkˢʳ-r ρ))
                 (hyp-ok (∈-map⁺ (mapᵈ wkʳ-v wkʳ-r) m)))

⊩ᴴ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} → wkᵉ-H Q ⊩ᴴ Q [ wkˢᵉ ]
⊩ᴴ-wkᵉ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkᵉ-tv Θ) m))
       (λ m → tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (wkᵉ-tv Θ)) m)))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢᵉ-r ρ)) (sym (wkˢᵉ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkᵉ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢᵉ-e ε)) (sym (wkˢᵉ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkᵉ-e) m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK (wkᵉ-H Q)) (sym (wkˢᵉ-v A)) (sym (wkˢᵉ-r ρ))
                 (hyp-ok (∈-map⁺ (mapᵈ wkᵉ-v wkᵉ-r) m)))

-- Entailment is preserved by the scope extensions

⊩-wkᵗᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkᵗ-H Q ⊩ wkᵗ-r ρ ≾̂ᵣ wkᵗ-r ρ'
⊩-wkᵗᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ᵣ y) (wkˢᵗ-r ρ) (wkˢᵗ-r ρ') (⊩-substᵣ ⊩ᴴ-wkᵗ p)

⊩-wkᵗₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkᵗ-H Q ⊩ wkᵗ-e ε ≾̂ₑ wkᵗ-e ε'
⊩-wkᵗₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ₑ y) (wkˢᵗ-e ε) (wkˢᵗ-e ε') (⊩-substₑ ⊩ᴴ-wkᵗ p)

⊩ᴱ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkᵗ-H Q ⊩ᴱ wkᵗ-v A
⊩ᴱ-wkᵗ {Q = Q} {A} et =
  subst (λ x → wkᵗ-H Q ⊩ᴱ x) (wkˢᵗ-v A) (⊩ᴱ-subst ⊩ᴴ-wkᵗ et)

<:̂ᵛ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵗ-H Q ∣ wkᵗ-v A <:̂ᵛ wkᵗ-v A'
<:̂ᵛ-wkᵗ {Q = Q} {A} {A'} p =
  subst₂ (wkᵗ-H Q ∣_<:̂ᵛ_) (wkˢᵗ-v A) (wkˢᵗ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵗ p)

⊩-wkʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkʳ-H Q ⊩ wkʳ-r ρ ≾̂ᵣ wkʳ-r ρ'
⊩-wkʳᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ᵣ y) (wkˢʳ-r ρ) (wkˢʳ-r ρ') (⊩-substᵣ ⊩ᴴ-wkʳ p)

⊩-wkʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkʳ-H Q ⊩ wkʳ-e ε ≾̂ₑ wkʳ-e ε'
⊩-wkʳₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ₑ y) (wkˢʳ-e ε) (wkˢʳ-e ε') (⊩-substₑ ⊩ᴴ-wkʳ p)

⊩ᴱ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkʳ-H Q ⊩ᴱ wkʳ-v A
⊩ᴱ-wkʳ {Q = Q} {A} et =
  subst (λ x → wkʳ-H Q ⊩ᴱ x) (wkˢʳ-v A) (⊩ᴱ-subst ⊩ᴴ-wkʳ et)

<:̂ᵛ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkʳ-H Q ∣ wkʳ-v A <:̂ᵛ wkʳ-v A'
<:̂ᵛ-wkʳ {Q = Q} {A} {A'} p =
  subst₂ (wkʳ-H Q ∣_<:̂ᵛ_) (wkˢʳ-v A) (wkˢʳ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkʳ p)

⊩-wkᵉᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkᵉ-H Q ⊩ wkᵉ-r ρ ≾̂ᵣ wkᵉ-r ρ'
⊩-wkᵉᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (wkˢᵉ-r ρ) (wkˢᵉ-r ρ') (⊩-substᵣ ⊩ᴴ-wkᵉ p)

⊩-wkᵉₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkᵉ-H Q ⊩ wkᵉ-e ε ≾̂ₑ wkᵉ-e ε'
⊩-wkᵉₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (wkˢᵉ-e ε) (wkˢᵉ-e ε') (⊩-substₑ ⊩ᴴ-wkᵉ p)

⊩ᴱ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkᵉ-H Q ⊩ᴱ wkᵉ-v A
⊩ᴱ-wkᵉ {Q = Q} {A} et =
  subst (λ x → wkᵉ-H Q ⊩ᴱ x) (wkˢᵉ-v A) (⊩ᴱ-subst ⊩ᴴ-wkᵉ et)

VarOK-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A ρ}
          → VarOK Q A ρ → VarOK (wkᵉ-H Q) (wkᵉ-v A) (wkᵉ-r ρ)
VarOK-wkᵉ {Q = Q} {A} {ρ} ok =
  subst₂ (VarOK (wkᵉ-H Q)) (wkˢᵉ-v A) (wkˢᵉ-r ρ) (VarOK-subst ⊩ᴴ-wkᵉ ok)

<:̂ᵛ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵉ-H Q ∣ wkᵉ-v A <:̂ᵛ wkᵉ-v A'
<:̂ᵛ-wkᵉ {Q = Q} {A} {A'} p =
  subst₂ (wkᵉ-H Q ∣_<:̂ᵛ_) (wkˢᵉ-v A) (wkˢᵉ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵉ p)
