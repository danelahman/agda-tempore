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

-- Antisymmetry, so subtyping is a partial order on types. The grade
-- positions are settled by antisymmetry of the grade orders, taken with
-- the two bounds in the order the variance dictates.

<:ᵛ-antisym : ∀ {A B} → A <:ᵛ B → B <:ᵛ A → A ≡ B
<:ᶜ-antisym : ∀ {C₁ C₂} → C₁ <:ᶜ C₂ → C₂ <:ᶜ C₁ → C₁ ≡ C₂

<:ᵛ-antisym (Baseₛ p)  (Baseₛ _)  = cong Base p
<:ᵛ-antisym Unitₛ      Unitₛ      = refl
<:ᵛ-antisym Boolₛ      Boolₛ      = refl
<:ᵛ-antisym (p |×|ₛ r) (q |×|ₛ s) =
  cong₂ _|×|_ (<:ᵛ-antisym p q) (<:ᵛ-antisym r s)
<:ᵛ-antisym Emptyₛ     Emptyₛ     = refl
<:ᵛ-antisym (p ⇒ₛ r)   (q ⇒ₛ s)   =
  cong₂ _⇒_ (<:ᵛ-antisym q p) (<:ᶜ-antisym r s)
<:ᵛ-antisym ([ p ]ₛ r) ([ q ]ₛ s) =
  cong₂ [_]_ (≾ᵣ-antisym q p) (<:ᵛ-antisym r s)

<:ᶜ-antisym (p ‼ₛ r) (q ‼ₛ s) = cong₂ _‼_ (<:ᵛ-antisym p q) (≾ₑ-antisym r s)

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


-------------------------------------------------------------------
-- Least upper bounds of value and computation types              --
--                                                                --
-- `A₁ ⊔ᵛ A₂ ≡ A` says that `A` is a least upper bound of `A₁`    --
-- and `A₂` for `_<:ᵛ_`. A ternary inductive family in the same   --
-- style as `_<:ᵛ_`: one constructor per matching pair of type    --
-- formers, so mismatched shapes are uninhabited and the joined   --
-- type is read off structurally.                                 --
--                                                                --
-- The relation is partial, and deliberately so: a function's     --
-- domain and a box's grade are contravariant, so joining them    --
-- would ask for *meets* of value types and of resource grades,   --
-- neither of which is available. Those two positions are         --
-- therefore pinned — one shared domain, one shared grade — and   --
-- the only component genuinely joined is a computation's effect, --
-- where `_⊔ₑ_` always exists.                                    --
--                                                                --
-- The constructors and their premises are instances: the         --
-- relation is syntax-directed on its two input types, so a       --
-- witness is found by instance search and reads as a side        --
-- condition on a rule rather than as a premise of it.            --
-------------------------------------------------------------------

infix 4 _⊔ᵛ_≡_ _⊔ᶜ_≡_

data _⊔ᵛ_≡_ : VType → VType → VType → Set
data _⊔ᶜ_≡_ : CType → CType → CType → Set

data _⊔ᵛ_≡_ where
  instance
    Baseⱼ  : ∀ {b} → Base b ⊔ᵛ Base b ≡ Base b
    Unitⱼ  : Unit ⊔ᵛ Unit ≡ Unit
    Boolⱼ  : Bool ⊔ᵛ Bool ≡ Bool
    |×|ⱼ   : ∀ {A₁ A₂ A B₁ B₂ B}
           → {{A₁ ⊔ᵛ A₂ ≡ A}}
           → {{B₁ ⊔ᵛ B₂ ≡ B}}
           → (A₁ |×| B₁) ⊔ᵛ (A₂ |×| B₂) ≡ (A |×| B)
    Emptyⱼ : Empty ⊔ᵛ Empty ≡ Empty
    ⇒ⱼ     : ∀ {A C₁ C₂ C}
           → {{C₁ ⊔ᶜ C₂ ≡ C}}
           → (A ⇒ C₁) ⊔ᵛ (A ⇒ C₂) ≡ (A ⇒ C)
    []ⱼ    : ∀ {ρ A₁ A₂ A}
           → {{A₁ ⊔ᵛ A₂ ≡ A}}
           → ([ ρ ] A₁) ⊔ᵛ ([ ρ ] A₂) ≡ ([ ρ ] A)

data _⊔ᶜ_≡_ where
  instance
    ‼ⱼ : ∀ {A₁ A₂ A ε₁ ε₂}
       → {{A₁ ⊔ᵛ A₂ ≡ A}}
       → (A₁ ‼ ε₁) ⊔ᶜ (A₂ ‼ ε₂) ≡ (A ‼ (ε₁ ⊔ₑ ε₂))

-- The join is an upper bound of both arguments

⊔ᵛ-ubˡ : ∀ {A₁ A₂ A} → A₁ ⊔ᵛ A₂ ≡ A → A₁ <:ᵛ A
⊔ᶜ-ubˡ : ∀ {C₁ C₂ C} → C₁ ⊔ᶜ C₂ ≡ C → C₁ <:ᶜ C

⊔ᵛ-ubˡ Baseⱼ              = Baseₛ refl
⊔ᵛ-ubˡ Unitⱼ              = Unitₛ
⊔ᵛ-ubˡ Boolⱼ              = Boolₛ
⊔ᵛ-ubˡ Emptyⱼ             = Emptyₛ
⊔ᵛ-ubˡ (|×|ⱼ {{j}} {{k}}) = ⊔ᵛ-ubˡ j |×|ₛ ⊔ᵛ-ubˡ k
⊔ᵛ-ubˡ (⇒ⱼ {{j}})         = <:ᵛ-refl _ ⇒ₛ ⊔ᶜ-ubˡ j
⊔ᵛ-ubˡ ([]ⱼ {{j}})        = [ ≾ᵣ-refl ]ₛ ⊔ᵛ-ubˡ j

⊔ᶜ-ubˡ (‼ⱼ {{j}}) = ⊔ᵛ-ubˡ j ‼ₛ ⊔ₑ-ubˡ _ _

⊔ᵛ-ubʳ : ∀ {A₁ A₂ A} → A₁ ⊔ᵛ A₂ ≡ A → A₂ <:ᵛ A
⊔ᶜ-ubʳ : ∀ {C₁ C₂ C} → C₁ ⊔ᶜ C₂ ≡ C → C₂ <:ᶜ C

⊔ᵛ-ubʳ Baseⱼ              = Baseₛ refl
⊔ᵛ-ubʳ Unitⱼ              = Unitₛ
⊔ᵛ-ubʳ Boolⱼ              = Boolₛ
⊔ᵛ-ubʳ Emptyⱼ             = Emptyₛ
⊔ᵛ-ubʳ (|×|ⱼ {{j}} {{k}}) = ⊔ᵛ-ubʳ j |×|ₛ ⊔ᵛ-ubʳ k
⊔ᵛ-ubʳ (⇒ⱼ {{j}})         = <:ᵛ-refl _ ⇒ₛ ⊔ᶜ-ubʳ j
⊔ᵛ-ubʳ ([]ⱼ {{j}})        = [ ≾ᵣ-refl ]ₛ ⊔ᵛ-ubʳ j

⊔ᶜ-ubʳ (‼ⱼ {{j}}) = ⊔ᵛ-ubʳ j ‼ₛ ⊔ₑ-ubʳ _ _

-- The join is below any common upper bound.
--
-- The pinned positions are what makes this go through with no meets: at a
-- box the bound is `[ σ ] Z` and its own `σ ≾ᵣ ρ` is the bound the joined
-- type needs, and at an arrow the bound's `A' <:ᵛ A` is reusable verbatim
-- because the domain is shared.

⊔ᵛ-lub : ∀ {A₁ A₂ A B} → A₁ ⊔ᵛ A₂ ≡ A → A₁ <:ᵛ B → A₂ <:ᵛ B → A <:ᵛ B
⊔ᶜ-lub : ∀ {C₁ C₂ C D} → C₁ ⊔ᶜ C₂ ≡ C → C₁ <:ᶜ D → C₂ <:ᶜ D → C <:ᶜ D

⊔ᵛ-lub Baseⱼ  p          _          = p
⊔ᵛ-lub Unitⱼ  p          _          = p
⊔ᵛ-lub Boolⱼ  p          _          = p
⊔ᵛ-lub Emptyⱼ p          _          = p
⊔ᵛ-lub (|×|ⱼ {{j}} {{k}}) (p |×|ₛ r) (q |×|ₛ s) =
  ⊔ᵛ-lub j p q |×|ₛ ⊔ᵛ-lub k r s
⊔ᵛ-lub (⇒ⱼ {{j}})  (p ⇒ₛ r)   (_ ⇒ₛ s)   = p ⇒ₛ ⊔ᶜ-lub j r s
⊔ᵛ-lub ([]ⱼ {{j}}) ([ p ]ₛ r) ([ _ ]ₛ s) = [ p ]ₛ ⊔ᵛ-lub j r s

⊔ᶜ-lub (‼ⱼ {{j}}) (p ‼ₛ r) (q ‼ₛ s) = ⊔ᵛ-lub j p q ‼ₛ ⊔ₑ-lub r s

-- The joined type is determined by the two arguments

⊔ᵛ-det : ∀ {A₁ A₂ A A'} → A₁ ⊔ᵛ A₂ ≡ A → A₁ ⊔ᵛ A₂ ≡ A' → A ≡ A'
⊔ᶜ-det : ∀ {C₁ C₂ C C'} → C₁ ⊔ᶜ C₂ ≡ C → C₁ ⊔ᶜ C₂ ≡ C' → C ≡ C'

⊔ᵛ-det Baseⱼ  Baseⱼ  = refl
⊔ᵛ-det Unitⱼ  Unitⱼ  = refl
⊔ᵛ-det Boolⱼ  Boolⱼ  = refl
⊔ᵛ-det Emptyⱼ Emptyⱼ = refl
⊔ᵛ-det (|×|ⱼ {{j}} {{k}}) (|×|ⱼ {{j'}} {{k'}}) =
  cong₂ _|×|_ (⊔ᵛ-det j j') (⊔ᵛ-det k k')
⊔ᵛ-det (⇒ⱼ {{j}})  (⇒ⱼ {{j'}})  = cong (_ ⇒_) (⊔ᶜ-det j j')
⊔ᵛ-det ([]ⱼ {{j}}) ([]ⱼ {{j'}}) = cong ([ _ ]_) (⊔ᵛ-det j j')

⊔ᶜ-det (‼ⱼ {{j}}) (‼ⱼ {{j'}}) = cong (_‼ _) (⊔ᵛ-det j j')

-- A type joined with itself is the type back again, on the nose.
--
-- The `‼` case is the one with a grade in it: `‼ⱼ` produces the effect
-- `ε ⊔ₑ ε`, which `⊔ₑ-idem` identifies with `ε`. Instance search does not
-- see through that equation, so the constructor is applied and transported
-- by hand.

⊔ᵛ-idem : (A : VType) → A ⊔ᵛ A ≡ A
⊔ᶜ-idem : (C : CType) → C ⊔ᶜ C ≡ C

⊔ᵛ-idem (Base b)  = Baseⱼ
⊔ᵛ-idem Unit      = Unitⱼ
⊔ᵛ-idem Bool      = Boolⱼ
⊔ᵛ-idem (A |×| B) = |×|ⱼ {{⊔ᵛ-idem A}} {{⊔ᵛ-idem B}}
⊔ᵛ-idem Empty     = Emptyⱼ
⊔ᵛ-idem (A ⇒ C)   = ⇒ⱼ {{⊔ᶜ-idem C}}
⊔ᵛ-idem ([ ρ ] A) = []ⱼ {{⊔ᵛ-idem A}}

⊔ᶜ-idem (A ‼ ε) =
  subst (λ x → (A ‼ ε) ⊔ᶜ (A ‼ ε) ≡ (A ‼ x)) (⊔ₑ-idem ε) (‼ⱼ {{⊔ᵛ-idem A}})
