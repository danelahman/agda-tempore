-------------------------------------------------------------------
-- Shape-preserving subtyping of value and computation types     --
--                                                               --
-- Structural inductive families: one constructor per pair of    --
-- matching type formers, and no `refl` or `trans` constructor,  --
-- so reflexivity, transitivity and proof irrelevance are lemmas --
-- and mismatched shapes are uninhabited.                        --
--                                                               --
-- A function's domain, a handler's handled computation and a    --
-- box's grade are contravariant, a computation's effect         --
-- covariant. The box direction agrees with `unbox`'s premise: a --
-- larger box grade is the weaker obligation.                    --
-------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import Data.Product using (proj₁; proj₂)

open import Util.Equality

module MonomorphicCalculus.Syntax.Subtyping (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Types S

infix  4  _<:ᵛ_ _<:ᶜ_
infix  37 [_]ₛ_
infix  32 _|×|ₛ_ _|+|ₛ_
infixr 30 _⇒ₛ_ _⇛ₛ_
infix  31 _!ₛ_

-- The relation

data _<:ᵛ_ : VType → VType → Set
data _<:ᶜ_ : CType → CType → Set

data _<:ᵛ_ where
  Baseₛ  : ∀ {b b'} → b ≡ b' → Base b <:ᵛ Base b'
  unitₛ  : unit <:ᵛ unit
  boolₛ  : bool <:ᵛ bool
  natₛ   : nat <:ᵛ nat
  _|×|ₛ_ : ∀ {A A' B B'} → A <:ᵛ A' → B <:ᵛ B' → (A |×| B) <:ᵛ (A' |×| B')
  _|+|ₛ_ : ∀ {A A' B B'} → A <:ᵛ A' → B <:ᵛ B' → (A |+| B) <:ᵛ (A' |+| B')
  listₛ  : ∀ {A A'} → A <:ᵛ A' → (list A) <:ᵛ (list A')
  emptyₛ : empty <:ᵛ empty
  _⇒ₛ_   : ∀ {A A' C C'} → A' <:ᵛ A → C <:ᶜ C' → (A ⇒ C) <:ᵛ (A' ⇒ C')
  _⇛ₛ_   : ∀ {C C' D D'} → C' <:ᶜ C → D <:ᶜ D' → (C ⇛ D) <:ᵛ (C' ⇛ D')
  [_]ₛ_  : ∀ {ρ ρ' A A'} → ρ' ≾ᵣ ρ → A <:ᵛ A' → ([ ρ ] A) <:ᵛ ([ ρ' ] A')

data _<:ᶜ_ where
  _!ₛ_ : ∀ {A A' ε ε'} → A <:ᵛ A' → ε ≾ₑ ε' → (A ! ε) <:ᶜ (A' ! ε')

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
<:ᵛ-refl unit      = unitₛ
<:ᵛ-refl bool      = boolₛ
<:ᵛ-refl nat       = natₛ
<:ᵛ-refl (A |×| B) = <:ᵛ-refl A |×|ₛ <:ᵛ-refl B
<:ᵛ-refl (A |+| B) = <:ᵛ-refl A |+|ₛ <:ᵛ-refl B
<:ᵛ-refl (list A)  = listₛ (<:ᵛ-refl A)
<:ᵛ-refl empty     = emptyₛ
<:ᵛ-refl (A ⇒ C)   = <:ᵛ-refl A ⇒ₛ <:ᶜ-refl C
<:ᵛ-refl (C ⇛ D)   = <:ᶜ-refl C ⇛ₛ <:ᶜ-refl D
<:ᵛ-refl ([ ρ ] A) = [ ≾ᵣ-refl ]ₛ <:ᵛ-refl A

<:ᶜ-refl (A ! ε) = <:ᵛ-refl A !ₛ ≾ₑ-refl

-- Transitivity; the contravariant positions compose in the opposite order

<:ᵛ-trans : ∀ {A B C} → A <:ᵛ B → B <:ᵛ C → A <:ᵛ C
<:ᶜ-trans : ∀ {C₁ C₂ C₃} → C₁ <:ᶜ C₂ → C₂ <:ᶜ C₃ → C₁ <:ᶜ C₃

<:ᵛ-trans (Baseₛ p)  (Baseₛ q)  = Baseₛ (trans p q)
<:ᵛ-trans unitₛ      unitₛ      = unitₛ
<:ᵛ-trans boolₛ      boolₛ      = boolₛ
<:ᵛ-trans natₛ       natₛ       = natₛ
<:ᵛ-trans (p |×|ₛ r) (q |×|ₛ s) = <:ᵛ-trans p q |×|ₛ <:ᵛ-trans r s
<:ᵛ-trans (p |+|ₛ r) (q |+|ₛ s) = <:ᵛ-trans p q |+|ₛ <:ᵛ-trans r s
<:ᵛ-trans (listₛ p)  (listₛ q)  = listₛ (<:ᵛ-trans p q)
<:ᵛ-trans emptyₛ     emptyₛ     = emptyₛ
<:ᵛ-trans (p ⇒ₛ r)   (q ⇒ₛ s)   = <:ᵛ-trans q p ⇒ₛ <:ᶜ-trans r s
<:ᵛ-trans (p ⇛ₛ r)   (q ⇛ₛ s)   = <:ᶜ-trans q p ⇛ₛ <:ᶜ-trans r s
<:ᵛ-trans ([ p ]ₛ r) ([ q ]ₛ s) = [ ≾ᵣ-trans q p ]ₛ <:ᵛ-trans r s

<:ᶜ-trans (p !ₛ r) (q !ₛ s) = <:ᵛ-trans p q !ₛ ≾ₑ-trans r s

-- Antisymmetry, where the grade orders are antisymmetric, so subtyping is
-- then a partial order on types. The grade positions are settled by
-- antisymmetry of the grade orders, taken with the two bounds in the order
-- the variance dictates.

module _ (≾ᵣ-antisym : ∀ {c d} → c ≾ᵣ d → d ≾ᵣ c → c ≡ d)
         (≾ₑ-antisym : ∀ {c d} → c ≾ₑ d → d ≾ₑ c → c ≡ d) where

  <:ᵛ-antisym : ∀ {A B} → A <:ᵛ B → B <:ᵛ A → A ≡ B
  <:ᶜ-antisym : ∀ {C₁ C₂} → C₁ <:ᶜ C₂ → C₂ <:ᶜ C₁ → C₁ ≡ C₂

  <:ᵛ-antisym (Baseₛ p)  (Baseₛ _)  = cong Base p
  <:ᵛ-antisym unitₛ      unitₛ      = refl
  <:ᵛ-antisym boolₛ      boolₛ      = refl
  <:ᵛ-antisym natₛ       natₛ       = refl
  <:ᵛ-antisym (p |×|ₛ r) (q |×|ₛ s) =
    cong₂ _|×|_ (<:ᵛ-antisym p q) (<:ᵛ-antisym r s)
  <:ᵛ-antisym (p |+|ₛ r) (q |+|ₛ s) =
    cong₂ _|+|_ (<:ᵛ-antisym p q) (<:ᵛ-antisym r s)
  <:ᵛ-antisym (listₛ p)  (listₛ q)  = cong list (<:ᵛ-antisym p q)
  <:ᵛ-antisym emptyₛ     emptyₛ     = refl
  <:ᵛ-antisym (p ⇒ₛ r)   (q ⇒ₛ s)   =
    cong₂ _⇒_ (<:ᵛ-antisym q p) (<:ᶜ-antisym r s)
  <:ᵛ-antisym (p ⇛ₛ r)   (q ⇛ₛ s)   =
    cong₂ _⇛_ (<:ᶜ-antisym q p) (<:ᶜ-antisym r s)
  <:ᵛ-antisym ([ p ]ₛ r) ([ q ]ₛ s) =
    cong₂ [_]_ (≾ᵣ-antisym q p) (<:ᵛ-antisym r s)

  <:ᶜ-antisym (p !ₛ r) (q !ₛ s) = cong₂ _!_ (<:ᵛ-antisym p q) (≾ₑ-antisym r s)

-- Subtyping is a property of a pair of types: any two witnesses
-- coincide, by irrelevance of the grade orderings and UIP at `Base`.

<:ᵛ-irrelevant : ∀ {A B} → (p q : A <:ᵛ B) → p ≡ q
<:ᶜ-irrelevant : ∀ {C₁ C₂} → (p q : C₁ <:ᶜ C₂) → p ≡ q

<:ᵛ-irrelevant (Baseₛ p)  (Baseₛ q)  = cong Baseₛ uip
<:ᵛ-irrelevant unitₛ      unitₛ      = refl
<:ᵛ-irrelevant boolₛ      boolₛ      = refl
<:ᵛ-irrelevant natₛ       natₛ       = refl
<:ᵛ-irrelevant (p |×|ₛ r) (q |×|ₛ s) =
  cong₂ _|×|ₛ_ (<:ᵛ-irrelevant p q) (<:ᵛ-irrelevant r s)
<:ᵛ-irrelevant (p |+|ₛ r) (q |+|ₛ s) =
  cong₂ _|+|ₛ_ (<:ᵛ-irrelevant p q) (<:ᵛ-irrelevant r s)
<:ᵛ-irrelevant (listₛ p)  (listₛ q)  = cong listₛ (<:ᵛ-irrelevant p q)
<:ᵛ-irrelevant emptyₛ     emptyₛ     = refl
<:ᵛ-irrelevant (p ⇒ₛ r)   (q ⇒ₛ s)   =
  cong₂ _⇒ₛ_ (<:ᵛ-irrelevant p q) (<:ᶜ-irrelevant r s)
<:ᵛ-irrelevant (p ⇛ₛ r)   (q ⇛ₛ s)   =
  cong₂ _⇛ₛ_ (<:ᶜ-irrelevant p q) (<:ᶜ-irrelevant r s)
<:ᵛ-irrelevant ([ p ]ₛ r) ([ q ]ₛ s) =
  cong₂ [_]ₛ_ (≾ᵣ-irrelevant p q) (<:ᵛ-irrelevant r s)

<:ᶜ-irrelevant (p !ₛ r) (q !ₛ s) =
  cong₂ _!ₛ_ (<:ᵛ-irrelevant p q) (≾ₑ-irrelevant r s)

-- Eternality lives on the shared skeleton (`Et` has no `_⇒_`, `_⇛_` or
-- `[_]_` clause, and the only grade it could see is a box's), so it transfers
-- along `_<:ᵛ_` in both directions.

<:ᵛ-eternalˡ : ∀ {A B} → A <:ᵛ B → Et B → Et A
<:ᵛ-eternalˡ (Baseₛ refl) et          = et
<:ᵛ-eternalˡ unitₛ        et          = et
<:ᵛ-eternalˡ boolₛ        et          = et
<:ᵛ-eternalˡ natₛ         et          = et
<:ᵛ-eternalˡ (p |×|ₛ r)   (et |×|ₑ e) = <:ᵛ-eternalˡ p et |×|ₑ <:ᵛ-eternalˡ r e
<:ᵛ-eternalˡ (p |+|ₛ r)   (et |+|ₑ e) = <:ᵛ-eternalˡ p et |+|ₑ <:ᵛ-eternalˡ r e
<:ᵛ-eternalˡ (listₛ p)     (listₑ et) = listₑ (<:ᵛ-eternalˡ p et)
<:ᵛ-eternalˡ emptyₛ       et          = et

<:ᵛ-eternalʳ : ∀ {A B} → A <:ᵛ B → Et A → Et B
<:ᵛ-eternalʳ (Baseₛ refl) et          = et
<:ᵛ-eternalʳ unitₛ        et          = et
<:ᵛ-eternalʳ boolₛ        et          = et
<:ᵛ-eternalʳ natₛ         et          = et
<:ᵛ-eternalʳ (p |×|ₛ r)   (et |×|ₑ e) = <:ᵛ-eternalʳ p et |×|ₑ <:ᵛ-eternalʳ r e
<:ᵛ-eternalʳ (p |+|ₛ r)   (et |+|ₑ e) = <:ᵛ-eternalʳ p et |+|ₑ <:ᵛ-eternalʳ r e
<:ᵛ-eternalʳ (listₛ p)     (listₑ et) = listₑ (<:ᵛ-eternalʳ p et)
<:ᵛ-eternalʳ emptyₛ       et          = et


-------------------------------------------------------------------
-- Least upper bounds of value and computation types             --
--                                                               --
-- `A₁ ⊔ᵛ A₂ ≡ A` says that `A` is a least upper bound of `A₁`   --
-- and `A₂` for `_<:ᵛ_`. A ternary inductive family in the same  --
-- style as `_<:ᵛ_`: one constructor per matching pair of type   --
-- formers, so mismatched shapes are uninhabited and the joined  --
-- type is read off structurally.                                --
--                                                               --
-- The relation is partial: a function's domain, a handler's     --
-- handled computation and a box's grade are contravariant, so   --
-- joining them would ask for meets of types and of grades,      --
-- which are not available. Those positions are pinned to one    --
-- shared domain and one shared grade, and only a computation's  --
-- effect is joined, where `_⊔ₑ_` always exists.                 --
--                                                               --
-- The constructors and their premises are instances: the        --
-- relation is syntax-directed on its two input types, so a      --
-- witness is found by instance search and reads as a side       --
-- condition on a rule rather than as a premise of it.           --
-------------------------------------------------------------------

infix 4 _⊔ᵛ_≡_ _⊔ᶜ_≡_

data _⊔ᵛ_≡_ : VType → VType → VType → Set
data _⊔ᶜ_≡_ : CType → CType → CType → Set

data _⊔ᵛ_≡_ where
  instance
    Baseⱼ  : ∀ {b} → Base b ⊔ᵛ Base b ≡ Base b
    unitⱼ  : unit ⊔ᵛ unit ≡ unit
    boolⱼ  : bool ⊔ᵛ bool ≡ bool
    natⱼ   : nat ⊔ᵛ nat ≡ nat
    |×|ⱼ   : ∀ {A₁ A₂ A B₁ B₂ B}
           → {{A₁ ⊔ᵛ A₂ ≡ A}}
           → {{B₁ ⊔ᵛ B₂ ≡ B}}
           → (A₁ |×| B₁) ⊔ᵛ (A₂ |×| B₂) ≡ (A |×| B)
    |+|ⱼ   : ∀ {A₁ A₂ A B₁ B₂ B}
           → {{A₁ ⊔ᵛ A₂ ≡ A}}
           → {{B₁ ⊔ᵛ B₂ ≡ B}}
           → (A₁ |+| B₁) ⊔ᵛ (A₂ |+| B₂) ≡ (A |+| B)
    listⱼ  : ∀ {A₁ A₂ A}
           → {{A₁ ⊔ᵛ A₂ ≡ A}}
           → (list A₁) ⊔ᵛ (list A₂) ≡ (list A)
    emptyⱼ : empty ⊔ᵛ empty ≡ empty
    ⇒ⱼ     : ∀ {A C₁ C₂ C}
           → {{C₁ ⊔ᶜ C₂ ≡ C}}
           → (A ⇒ C₁) ⊔ᵛ (A ⇒ C₂) ≡ (A ⇒ C)
    ⇛ⱼ     : ∀ {C D₁ D₂ D}
           → {{D₁ ⊔ᶜ D₂ ≡ D}}
           → (C ⇛ D₁) ⊔ᵛ (C ⇛ D₂) ≡ (C ⇛ D)
    []ⱼ    : ∀ {ρ A₁ A₂ A}
           → {{A₁ ⊔ᵛ A₂ ≡ A}}
           → ([ ρ ] A₁) ⊔ᵛ ([ ρ ] A₂) ≡ ([ ρ ] A)

data _⊔ᶜ_≡_ where
  instance
    !ⱼ : ∀ {A₁ A₂ A ε₁ ε₂}
       → {{A₁ ⊔ᵛ A₂ ≡ A}}
       → (A₁ ! ε₁) ⊔ᶜ (A₂ ! ε₂) ≡ (A ! (ε₁ ⊔ₑ ε₂))

-- The join is an upper bound of both arguments

⊔ᵛ-ubˡ : ∀ {A₁ A₂ A} → A₁ ⊔ᵛ A₂ ≡ A → A₁ <:ᵛ A
⊔ᶜ-ubˡ : ∀ {C₁ C₂ C} → C₁ ⊔ᶜ C₂ ≡ C → C₁ <:ᶜ C

⊔ᵛ-ubˡ Baseⱼ              = Baseₛ refl
⊔ᵛ-ubˡ unitⱼ              = unitₛ
⊔ᵛ-ubˡ boolⱼ              = boolₛ
⊔ᵛ-ubˡ natⱼ               = natₛ
⊔ᵛ-ubˡ emptyⱼ             = emptyₛ
⊔ᵛ-ubˡ (|×|ⱼ {{j}} {{k}}) = ⊔ᵛ-ubˡ j |×|ₛ ⊔ᵛ-ubˡ k
⊔ᵛ-ubˡ (|+|ⱼ {{j}} {{k}}) = ⊔ᵛ-ubˡ j |+|ₛ ⊔ᵛ-ubˡ k
⊔ᵛ-ubˡ (listⱼ {{j}})      = listₛ (⊔ᵛ-ubˡ j)
⊔ᵛ-ubˡ (⇒ⱼ {{j}})         = <:ᵛ-refl _ ⇒ₛ ⊔ᶜ-ubˡ j
⊔ᵛ-ubˡ (⇛ⱼ {{j}})         = <:ᶜ-refl _ ⇛ₛ ⊔ᶜ-ubˡ j
⊔ᵛ-ubˡ ([]ⱼ {{j}})        = [ ≾ᵣ-refl ]ₛ ⊔ᵛ-ubˡ j

⊔ᶜ-ubˡ (!ⱼ {{j}}) = ⊔ᵛ-ubˡ j !ₛ ⊔ₑ-ubˡ _ _

⊔ᵛ-ubʳ : ∀ {A₁ A₂ A} → A₁ ⊔ᵛ A₂ ≡ A → A₂ <:ᵛ A
⊔ᶜ-ubʳ : ∀ {C₁ C₂ C} → C₁ ⊔ᶜ C₂ ≡ C → C₂ <:ᶜ C

⊔ᵛ-ubʳ Baseⱼ              = Baseₛ refl
⊔ᵛ-ubʳ unitⱼ              = unitₛ
⊔ᵛ-ubʳ boolⱼ              = boolₛ
⊔ᵛ-ubʳ natⱼ               = natₛ
⊔ᵛ-ubʳ emptyⱼ             = emptyₛ
⊔ᵛ-ubʳ (|×|ⱼ {{j}} {{k}}) = ⊔ᵛ-ubʳ j |×|ₛ ⊔ᵛ-ubʳ k
⊔ᵛ-ubʳ (|+|ⱼ {{j}} {{k}}) = ⊔ᵛ-ubʳ j |+|ₛ ⊔ᵛ-ubʳ k
⊔ᵛ-ubʳ (listⱼ {{j}})      = listₛ (⊔ᵛ-ubʳ j)
⊔ᵛ-ubʳ (⇒ⱼ {{j}})         = <:ᵛ-refl _ ⇒ₛ ⊔ᶜ-ubʳ j
⊔ᵛ-ubʳ (⇛ⱼ {{j}})         = <:ᶜ-refl _ ⇛ₛ ⊔ᶜ-ubʳ j
⊔ᵛ-ubʳ ([]ⱼ {{j}})        = [ ≾ᵣ-refl ]ₛ ⊔ᵛ-ubʳ j

⊔ᶜ-ubʳ (!ⱼ {{j}}) = ⊔ᵛ-ubʳ j !ₛ ⊔ₑ-ubʳ _ _

-- The join is below any common upper bound.
--
-- The pinned positions are what makes this go through with no meets: at a
-- box the bound is `[ σ ] Z` and its own `σ ≾ᵣ ρ` is the bound the joined
-- type needs, and at an arrow the bound's `A' <:ᵛ A` is reusable verbatim
-- because the domain is shared.

⊔ᵛ-lub : ∀ {A₁ A₂ A B} → A₁ ⊔ᵛ A₂ ≡ A → A₁ <:ᵛ B → A₂ <:ᵛ B → A <:ᵛ B
⊔ᶜ-lub : ∀ {C₁ C₂ C D} → C₁ ⊔ᶜ C₂ ≡ C → C₁ <:ᶜ D → C₂ <:ᶜ D → C <:ᶜ D

⊔ᵛ-lub Baseⱼ  p          _          = p
⊔ᵛ-lub unitⱼ  p          _          = p
⊔ᵛ-lub boolⱼ  p          _          = p
⊔ᵛ-lub natⱼ   p          _          = p
⊔ᵛ-lub emptyⱼ p          _          = p
⊔ᵛ-lub (|×|ⱼ {{j}} {{k}}) (p |×|ₛ r) (q |×|ₛ s) =
  ⊔ᵛ-lub j p q |×|ₛ ⊔ᵛ-lub k r s
⊔ᵛ-lub (|+|ⱼ {{j}} {{k}}) (p |+|ₛ r) (q |+|ₛ s) =
  ⊔ᵛ-lub j p q |+|ₛ ⊔ᵛ-lub k r s
⊔ᵛ-lub (listⱼ {{j}}) (listₛ p) (listₛ q) = listₛ (⊔ᵛ-lub j p q)
⊔ᵛ-lub (⇒ⱼ {{j}})  (p ⇒ₛ r)   (_ ⇒ₛ s)   = p ⇒ₛ ⊔ᶜ-lub j r s
⊔ᵛ-lub (⇛ⱼ {{j}})  (p ⇛ₛ r)   (_ ⇛ₛ s)   = p ⇛ₛ ⊔ᶜ-lub j r s
⊔ᵛ-lub ([]ⱼ {{j}}) ([ p ]ₛ r) ([ _ ]ₛ s) = [ p ]ₛ ⊔ᵛ-lub j r s

⊔ᶜ-lub (!ⱼ {{j}}) (p !ₛ r) (q !ₛ s) = ⊔ᵛ-lub j p q !ₛ ⊔ₑ-lub r s

-- The joined type is determined by the two arguments

⊔ᵛ-det : ∀ {A₁ A₂ A A'} → A₁ ⊔ᵛ A₂ ≡ A → A₁ ⊔ᵛ A₂ ≡ A' → A ≡ A'
⊔ᶜ-det : ∀ {C₁ C₂ C C'} → C₁ ⊔ᶜ C₂ ≡ C → C₁ ⊔ᶜ C₂ ≡ C' → C ≡ C'

⊔ᵛ-det Baseⱼ  Baseⱼ  = refl
⊔ᵛ-det unitⱼ  unitⱼ  = refl
⊔ᵛ-det boolⱼ  boolⱼ  = refl
⊔ᵛ-det natⱼ   natⱼ   = refl
⊔ᵛ-det emptyⱼ emptyⱼ = refl
⊔ᵛ-det (|×|ⱼ {{j}} {{k}}) (|×|ⱼ {{j'}} {{k'}}) =
  cong₂ _|×|_ (⊔ᵛ-det j j') (⊔ᵛ-det k k')
⊔ᵛ-det (|+|ⱼ {{j}} {{k}}) (|+|ⱼ {{j'}} {{k'}}) =
  cong₂ _|+|_ (⊔ᵛ-det j j') (⊔ᵛ-det k k')
⊔ᵛ-det (listⱼ {{j}}) (listⱼ {{j'}}) = cong list (⊔ᵛ-det j j')
⊔ᵛ-det (⇒ⱼ {{j}})  (⇒ⱼ {{j'}})  = cong (_ ⇒_) (⊔ᶜ-det j j')
⊔ᵛ-det (⇛ⱼ {{j}})  (⇛ⱼ {{j'}})  = cong (_ ⇛_) (⊔ᶜ-det j j')
⊔ᵛ-det ([]ⱼ {{j}}) ([]ⱼ {{j'}}) = cong ([ _ ]_) (⊔ᵛ-det j j')

⊔ᶜ-det (!ⱼ {{j}}) (!ⱼ {{j'}}) = cong (_! _) (⊔ᵛ-det j j')

-- A type joined with itself is the type back again, on the nose where
-- the effect order is antisymmetric.
--
-- The `!` case is the one with a grade in it: `!ⱼ` produces the effect
-- `ε ⊔ₑ ε`, which `⊔ₑ-idem` makes equivalent to `ε`, and antisymmetry
-- equal. Instance search does not see through that equation, so the
-- constructor is applied and transported by hand.

module _ (≾ₑ-antisym : ∀ {c d} → c ≾ₑ d → d ≾ₑ c → c ≡ d) where

  ⊔ᵛ-idem : (A : VType) → A ⊔ᵛ A ≡ A
  ⊔ᶜ-idem : (C : CType) → C ⊔ᶜ C ≡ C

  ⊔ᵛ-idem (Base b)  = Baseⱼ
  ⊔ᵛ-idem unit      = unitⱼ
  ⊔ᵛ-idem bool      = boolⱼ
  ⊔ᵛ-idem nat       = natⱼ
  ⊔ᵛ-idem (A |×| B) = |×|ⱼ {{⊔ᵛ-idem A}} {{⊔ᵛ-idem B}}
  ⊔ᵛ-idem (A |+| B) = |+|ⱼ {{⊔ᵛ-idem A}} {{⊔ᵛ-idem B}}
  ⊔ᵛ-idem (list A)  = listⱼ {{⊔ᵛ-idem A}}
  ⊔ᵛ-idem empty     = emptyⱼ
  ⊔ᵛ-idem (A ⇒ C)   = ⇒ⱼ {{⊔ᶜ-idem C}}
  ⊔ᵛ-idem (C ⇛ D)   = ⇛ⱼ {{⊔ᶜ-idem D}}
  ⊔ᵛ-idem ([ ρ ] A) = []ⱼ {{⊔ᵛ-idem A}}

  ⊔ᶜ-idem (A ! ε) =
    subst (λ x → (A ! ε) ⊔ᶜ (A ! ε) ≡ (A ! x))
          (≾ₑ-antisym (proj₁ (⊔ₑ-idem ε)) (proj₂ (⊔ₑ-idem ε)))
          (!ⱼ {{⊔ᵛ-idem A}})
