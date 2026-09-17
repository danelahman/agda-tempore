------------------------------------------------------------------
-- Hypotheses and entailment of the mirrored language             --
--                                                                --
-- A hypothesis set `Hyps Θ` collects the eternality atoms on     --
-- type variables and the assumed orderings between open grade    --
-- expressions under which a mirrored typing derivation is built. --
-- Entailment (`_⊩_≾̂ᵣ_`, `_⊩_≾̂ₑ_`, `_⊩ᴱ_`) is an inductive       --
-- under-approximation of truth in all groundings.                --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Product using (_×_; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Inference.Scopes

module Inference.Open.Hyps (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- Only the eternal-base-type predicate is needed; the constructors of the
-- closed `Eternal` are mirrored below and would otherwise clash.

open import Syntax.Types S using (EternalBaseType)

open import Inference.Open.Grades S
open import Inference.Open.Types  S
open import Inference.Open.Subst  S

-- Hypothesis sets

record Hyps (Θ : Scope) : Set where
  constructor hyps
  field
    ets  : List (TyVar Θ)                     -- eternality atoms on type variables
    ordᵣ : List (RExp Θ × RExp Θ)             -- assumed resource-grade orderings
    ordₑ : List (EExp Θ × EExp Θ)             -- assumed effect-grade orderings

open Hyps public

-- Empty hypothesis set

∅ᴴ : ∀ {Θ} → Hyps Θ
∅ᴴ = hyps [] [] []

-- Pairwise action of a function on a homogeneous pair

mapᵖ : ∀ {A B : Set} → (A → B) → A × A → B × B
mapᵖ f (x , y) = f x , f y

-- Action of the scope extensions on hypothesis sets

wkᵗ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +ty)
wkᵗ-H {Θ} Q = hyps (map (wkᵗ-tv Θ) (ets Q))
                   (map (mapᵖ wkᵗ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵗ-e) (ordₑ Q))

wkʳ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +r)
wkʳ-H {Θ} Q = hyps (map (wkʳ-tv Θ) (ets Q))
                   (map (mapᵖ wkʳ-r) (ordᵣ Q))
                   (map (mapᵖ wkʳ-e) (ordₑ Q))

wkᵉ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +e)
wkᵉ-H {Θ} Q = hyps (map (wkᵉ-tv Θ) (ets Q))
                   (map (mapᵖ wkᵉ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵉ-e) (ordₑ Q))

--------------------------------------------------------------
-- Convertibility of open grade expressions                  --
--                                                           --
-- The monoid laws, the constants' arithmetic, and the fact   --
-- that `∣_∣̂ᵉ` is a monoid morphism. No hypotheses involved.  --
--------------------------------------------------------------

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

--------------------------------------------------------------
-- Entailment of grade orderings                             --
--------------------------------------------------------------

infix 4 _⊩_≾̂ᵣ_ _⊩_≾̂ₑ_

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

data _⊩_≾̂ₑ_ {Θ} Q where
  hypₑ   : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q ⊩ ε ≾̂ₑ ε'
  atomₑ  : ∀ {ε ε'} → ε ≾ₑ ε' → Q ⊩ econst ε ≾̂ₑ econst ε'
  eqₑ    : ∀ {ε ε'} → ε ≡̂ₑ ε' → Q ⊩ ε ≾̂ₑ ε'
  transₑ : ∀ {ε ε' ε''} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ε' ≾̂ₑ ε'' → Q ⊩ ε ≾̂ₑ ε''
  monoₑ  : ∀ {ε₁ ε₁' ε₂ ε₂'} → Q ⊩ ε₁ ≾̂ₑ ε₁' → Q ⊩ ε₂ ≾̂ₑ ε₂'
         → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ ε₁' ·̂ₑ ε₂'

-- Entailed ordering is reflexive

⊩≾̂ᵣ-refl : ∀ {Θ} {Q : Hyps Θ} {ρ} → Q ⊩ ρ ≾̂ᵣ ρ
⊩≾̂ᵣ-refl = eqᵣ ≡̂ᵣ-refl

⊩≾̂ₑ-refl : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ≾̂ₑ ε
⊩≾̂ₑ-refl = eqₑ ≡̂ₑ-refl

--------------------------------------------------------------
-- Entailment of eternality                                  --
--                                                           --
-- Mirrors `Eternal` of `Syntax.Types`, with an extra rule    --
-- for the eternality atoms of the hypothesis set. As in the  --
-- original, there is no rule for `_⇒_` and `[_]_`.           --
--------------------------------------------------------------

infix 4 _⊩ᴱ_

data _⊩ᴱ_ {Θ : Scope} (Q : Hyps Θ) : OVType Θ → Set where
  et-hyp : ∀ {α} → α ∈ ets Q → Q ⊩ᴱ tvar α
  Baseₑ  : ∀ {b} → .(EternalBaseType b) → Q ⊩ᴱ Base b
  Unitₑ  : Q ⊩ᴱ Unit
  Boolₑ  : Q ⊩ᴱ Bool
  _|×|ₑ_ : ∀ {A₁ A₂} → Q ⊩ᴱ A₁ → Q ⊩ᴱ A₂ → Q ⊩ᴱ A₁ |×| A₂
  Emptyₑ : Q ⊩ᴱ Empty

--------------------------------------------------------------
-- Entailment between hypothesis sets                        --
--                                                           --
-- `Q' ⊩ᴴ Q [ σ ]` says that `Q'` entails every hypothesis of --
-- `Q` transported along `σ`. There is no syntactic action of --
-- a substitution on `Hyps`: `ets` holds *variables*, whose   --
-- images under `σ` are open types, not variables.            --
--------------------------------------------------------------

infix 4 _⊩ᴴ_[_] _⊩ᴴ_

record _⊩ᴴ_[_] {Θ Θ' : Scope} (Q' : Hyps Θ') (Q : Hyps Θ) (σ : Subst Θ Θ') : Set where
  constructor mk⊩ᴴ
  field
    ⊩ets  : ∀ {α} → α ∈ ets Q → Q' ⊩ᴱ sTy σ α
    ⊩ordᵣ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
    ⊩ordₑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ

open _⊩ᴴ_[_] public

-- Entailment between hypothesis sets over the same scope

_⊩ᴴ_ : ∀ {Θ} → Hyps Θ → Hyps Θ → Set
Q' ⊩ᴴ Q = Q' ⊩ᴴ Q [ idˢ ]

--------------------------------------------------------------
-- Stability of convertibility under substitution            --
--------------------------------------------------------------

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

--------------------------------------------------------------
-- Stability of entailment under substitution                --
--------------------------------------------------------------

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

⊩-substₑ         h (hypₑ m)     = ⊩ordₑ h m
⊩-substₑ         h (atomₑ p)    = atomₑ p
⊩-substₑ {σ = σ} h (eqₑ p)      = eqₑ (≡̂ₑ-subst σ p)
⊩-substₑ         h (transₑ p q) = transₑ (⊩-substₑ h p) (⊩-substₑ h q)
⊩-substₑ         h (monoₑ p q)  = monoₑ (⊩-substₑ h p) (⊩-substₑ h q)

⊩ᴱ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A : OVType Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ᴱ A → Q' ⊩ᴱ A [ σ ]ᵛ
⊩ᴱ-subst h (et-hyp m)  = ⊩ets h m
⊩ᴱ-subst h (Baseₑ p)   = Baseₑ p
⊩ᴱ-subst h Unitₑ       = Unitₑ
⊩ᴱ-subst h Boolₑ       = Boolₑ
⊩ᴱ-subst h (et₁ |×|ₑ et₂) = ⊩ᴱ-subst h et₁ |×|ₑ ⊩ᴱ-subst h et₂
⊩ᴱ-subst h Emptyₑ      = Emptyₑ

--------------------------------------------------------------
-- Identity and composition of hypothesis entailment         --
--------------------------------------------------------------

⊩ᴴ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ᴴ Q [ idˢ ]
⊩ᴴ-refl {Q = Q} =
  mk⊩ᴴ et-hyp
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ')) (hypᵣ m))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε')) (hypₑ m))

⊩ᴴ-⨟ : ∀ {Θ Θ' Θ''} {Q : Hyps Θ} {Q' : Hyps Θ'} {Q'' : Hyps Θ''}
       {σ : Subst Θ Θ'} {δ : Subst Θ' Θ''}
     → Q'' ⊩ᴴ Q' [ δ ] → Q' ⊩ᴴ Q [ σ ] → Q'' ⊩ᴴ Q [ σ ⨟ˢ δ ]
⊩ᴴ-⨟ {Q'' = Q''} {σ = σ} {δ = δ} h' h =
  mk⊩ᴴ (λ m → ⊩ᴱ-subst h' (⊩ets h m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q'' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
                 (⊩-substᵣ h' (⊩ordᵣ h m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q'' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)
                 (⊩-substₑ h' (⊩ordₑ h m)))

--------------------------------------------------------------
-- Compatibility with the scope extensions                   --
--                                                           --
-- Weakening a hypothesis set is the action of the weakening --
-- substitution, so entailment is stable under it.           --
--------------------------------------------------------------

⊩ᴴ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} → wkᵗ-H Q ⊩ᴴ Q [ wkˢᵗ ]
⊩ᴴ-wkᵗ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkᵗ-tv Θ) m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢᵗ-r ρ)) (sym (wkˢᵗ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkᵗ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢᵗ-e ε)) (sym (wkˢᵗ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkᵗ-e) m)))

⊩ᴴ-wkʳ : ∀ {Θ} {Q : Hyps Θ} → wkʳ-H Q ⊩ᴴ Q [ wkˢʳ ]
⊩ᴴ-wkʳ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkʳ-tv Θ) m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢʳ-r ρ)) (sym (wkˢʳ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkʳ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢʳ-e ε)) (sym (wkˢʳ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkʳ-e) m)))

⊩ᴴ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} → wkᵉ-H Q ⊩ᴴ Q [ wkˢᵉ ]
⊩ᴴ-wkᵉ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkᵉ-tv Θ) m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢᵉ-r ρ)) (sym (wkˢᵉ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkᵉ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢᵉ-e ε)) (sym (wkˢᵉ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkᵉ-e) m)))

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

⊩-wkʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkʳ-H Q ⊩ wkʳ-r ρ ≾̂ᵣ wkʳ-r ρ'
⊩-wkʳᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ᵣ y) (wkˢʳ-r ρ) (wkˢʳ-r ρ') (⊩-substᵣ ⊩ᴴ-wkʳ p)

⊩-wkʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkʳ-H Q ⊩ wkʳ-e ε ≾̂ₑ wkʳ-e ε'
⊩-wkʳₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ₑ y) (wkˢʳ-e ε) (wkˢʳ-e ε') (⊩-substₑ ⊩ᴴ-wkʳ p)

⊩ᴱ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkʳ-H Q ⊩ᴱ wkʳ-v A
⊩ᴱ-wkʳ {Q = Q} {A} et =
  subst (λ x → wkʳ-H Q ⊩ᴱ x) (wkˢʳ-v A) (⊩ᴱ-subst ⊩ᴴ-wkʳ et)

⊩-wkᵉᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkᵉ-H Q ⊩ wkᵉ-r ρ ≾̂ᵣ wkᵉ-r ρ'
⊩-wkᵉᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (wkˢᵉ-r ρ) (wkˢᵉ-r ρ') (⊩-substᵣ ⊩ᴴ-wkᵉ p)

⊩-wkᵉₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkᵉ-H Q ⊩ wkᵉ-e ε ≾̂ₑ wkᵉ-e ε'
⊩-wkᵉₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (wkˢᵉ-e ε) (wkˢᵉ-e ε') (⊩-substₑ ⊩ᴴ-wkᵉ p)

⊩ᴱ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkᵉ-H Q ⊩ᴱ wkᵉ-v A
⊩ᴱ-wkᵉ {Q = Q} {A} et =
  subst (λ x → wkᵉ-H Q ⊩ᴱ x) (wkˢᵉ-v A) (⊩ᴱ-subst ⊩ᴴ-wkᵉ et)
