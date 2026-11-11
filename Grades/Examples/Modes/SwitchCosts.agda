------------------------------------------------------------------------
-- Mode-switch costs: the costs of a computation between the modes of --
-- a device, such as a radio switched on and off.                     --
--                                                                    --
-- A grade gives each pair of modes `(p , q)` the greatest cost of    --
-- the traces that start in `p` and end in `q`, or `none` if there is --
-- no such trace. The costs form the max-plus dioid: no trace, below  --
-- the natural numbers, below `∞`; the join is the maximum and the    --
-- product the sum, `none` absorbing and then `∞`. A grade is a mode  --
-- matrix over it, the costs naming no modes (the trivial action,     --
-- `Matrix.ModeGrade`): total, its only trace from `stuck` to `stuck` --
-- at cost 0, and each change between two distinct ordinary modes     --
-- costing at least 1. Sequencing is the max-plus                     --
-- product; the unit keeps every mode at cost 0 and is not least, the --
-- product does not commute, and delays keep the mode at no cost.     --
-- Modes are named by natural numbers.                                --
--                                                                    --
-- Literals list entries `(from , to , cost)`, the modes not named    --
-- written `⋆`, another one `⋆'` and `stuck` `✗`; a mode from which   --
-- no entry starts is stuck at cost 0 (`listing`).                    --
------------------------------------------------------------------------

module Grades.Examples.Modes.SwitchCosts where

open import Data.Bool.Base using (Bool; true; false; _∨_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; concatMap)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s; _≡ᵇ_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (_⊎-dec_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations using (Duration)
open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-infinite)
open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Matrix.Dioid using (Dioid)
open import Function.Base using (_$_)

open import Util.Equality

------------------------------------------------------------------------
-- The costs

data Cost : Set where
  none      : Cost
  cost      : ℕ → Cost
  unbounded : Cost

infix  4 _≤ᶜ_
infixl 6 _⊕ᶜ_
infixl 7 _⊗ᶜ_

data _≤ᶜ_ : Cost → Cost → Set where
  none≤    : ∀ {c} → none ≤ᶜ c
  cost≤    : ∀ {m n} → m ≤ n → cost m ≤ᶜ cost n
  cost≤unb : ∀ {m} → cost m ≤ᶜ unbounded
  unb≤unb  : unbounded ≤ᶜ unbounded

_⊕ᶜ_ : Cost → Cost → Cost
none      ⊕ᶜ c         = c
cost m    ⊕ᶜ none      = cost m
cost m    ⊕ᶜ cost n    = cost (m ⊔ n)
cost _    ⊕ᶜ unbounded = unbounded
unbounded ⊕ᶜ _         = unbounded

_⊗ᶜ_ : Cost → Cost → Cost
none      ⊗ᶜ _         = none
cost _    ⊗ᶜ none      = none
cost m    ⊗ᶜ cost n    = cost (m + n)
cost _    ⊗ᶜ unbounded = unbounded
unbounded ⊗ᶜ none      = none
unbounded ⊗ᶜ _         = unbounded

≤ᶜ-refl : ∀ {c} → c ≤ᶜ c
≤ᶜ-refl {none}      = none≤
≤ᶜ-refl {cost _}    = cost≤ ℕₚ.≤-refl
≤ᶜ-refl {unbounded} = unb≤unb

≤ᶜ-trans : ∀ {a b c} → a ≤ᶜ b → b ≤ᶜ c → a ≤ᶜ c
≤ᶜ-trans none≤      _          = none≤
≤ᶜ-trans (cost≤ p)  (cost≤ q)  = cost≤ (ℕₚ.≤-trans p q)
≤ᶜ-trans (cost≤ _)  cost≤unb   = cost≤unb
≤ᶜ-trans cost≤unb   unb≤unb    = cost≤unb
≤ᶜ-trans unb≤unb    unb≤unb    = unb≤unb

≤ᶜ-irrelevant : ∀ {a b} (p q : a ≤ᶜ b) → p ≡ q
≤ᶜ-irrelevant none≤     none≤     = refl
≤ᶜ-irrelevant (cost≤ p) (cost≤ q) = cong cost≤ (ℕₚ.≤-irrelevant p q)
≤ᶜ-irrelevant cost≤unb  cost≤unb  = refl
≤ᶜ-irrelevant unb≤unb   unb≤unb   = refl

_≤ᶜ?_ : ∀ a b → Dec (a ≤ᶜ b)
none      ≤ᶜ? _         = yes none≤
cost m    ≤ᶜ? none      = no λ ()
cost m    ≤ᶜ? cost n with m ℕₚ.≤? n
... | yes p = yes (cost≤ p)
... | no ¬p = no λ { (cost≤ p) → ¬p p }
cost m    ≤ᶜ? unbounded = yes cost≤unb
unbounded ≤ᶜ? none      = no λ ()
unbounded ≤ᶜ? cost _    = no λ ()
unbounded ≤ᶜ? unbounded = yes unb≤unb

≤ᶜ-unb : ∀ c → c ≤ᶜ unbounded
≤ᶜ-unb none      = none≤
≤ᶜ-unb (cost _)  = cost≤unb
≤ᶜ-unb unbounded = unb≤unb

⊕ᶜ-ubˡ : ∀ a b → a ≤ᶜ a ⊕ᶜ b
⊕ᶜ-ubˡ none      b         = none≤
⊕ᶜ-ubˡ (cost m)  none      = ≤ᶜ-refl
⊕ᶜ-ubˡ (cost m)  (cost n)  = cost≤ (ℕₚ.m≤m⊔n m n)
⊕ᶜ-ubˡ (cost m)  unbounded = cost≤unb
⊕ᶜ-ubˡ unbounded b         = unb≤unb

⊕ᶜ-ubʳ : ∀ a b → b ≤ᶜ a ⊕ᶜ b
⊕ᶜ-ubʳ none      b         = ≤ᶜ-refl
⊕ᶜ-ubʳ (cost m)  none      = none≤
⊕ᶜ-ubʳ (cost m)  (cost n)  = cost≤ (ℕₚ.m≤n⊔m m n)
⊕ᶜ-ubʳ (cost m)  unbounded = unb≤unb
⊕ᶜ-ubʳ unbounded b         = ≤ᶜ-unb b

⊕ᶜ-lub : ∀ {a b c} → a ≤ᶜ c → b ≤ᶜ c → a ⊕ᶜ b ≤ᶜ c
⊕ᶜ-lub none≤      q          = q
⊕ᶜ-lub (cost≤ p)  none≤      = cost≤ p
⊕ᶜ-lub (cost≤ p)  (cost≤ q)  = cost≤ (ℕₚ.⊔-lub p q)
⊕ᶜ-lub cost≤unb   _          = ≤ᶜ-unb _
⊕ᶜ-lub unb≤unb    _          = unb≤unb

⊗ᶜ-mono : ∀ {a a' b b'} → a ≤ᶜ a' → b ≤ᶜ b' → a ⊗ᶜ b ≤ᶜ a' ⊗ᶜ b'
⊗ᶜ-mono none≤ _ = none≤
⊗ᶜ-mono (cost≤ p) none≤ = none≤
⊗ᶜ-mono (cost≤ p) (cost≤ q) = cost≤ (ℕₚ.+-mono-≤ p q)
⊗ᶜ-mono (cost≤ p) cost≤unb = cost≤unb
⊗ᶜ-mono (cost≤ p) unb≤unb = unb≤unb
⊗ᶜ-mono cost≤unb none≤ = none≤
⊗ᶜ-mono cost≤unb (cost≤ q) = cost≤unb
⊗ᶜ-mono cost≤unb cost≤unb = cost≤unb
⊗ᶜ-mono cost≤unb unb≤unb = unb≤unb
⊗ᶜ-mono unb≤unb none≤ = none≤
⊗ᶜ-mono unb≤unb (cost≤ _) = unb≤unb
⊗ᶜ-mono unb≤unb cost≤unb = unb≤unb
⊗ᶜ-mono unb≤unb unb≤unb = unb≤unb

private
  ≡⇒≈ : ∀ {a b} → a ≡ b → (a ≤ᶜ b) × (b ≤ᶜ a)
  ≡⇒≈ refl = ≤ᶜ-refl , ≤ᶜ-refl

⊗ᶜ-identityˡ : ∀ a → cost 0 ⊗ᶜ a ≡ a
⊗ᶜ-identityˡ none      = refl
⊗ᶜ-identityˡ (cost _)  = refl
⊗ᶜ-identityˡ unbounded = refl

⊗ᶜ-identityʳ : ∀ a → a ⊗ᶜ cost 0 ≡ a
⊗ᶜ-identityʳ none      = refl
⊗ᶜ-identityʳ (cost m)  = cong cost (ℕₚ.+-identityʳ m)
⊗ᶜ-identityʳ unbounded = refl

⊗ᶜ-assoc : ∀ a b c → (a ⊗ᶜ b) ⊗ᶜ c ≡ a ⊗ᶜ (b ⊗ᶜ c)
⊗ᶜ-assoc none      b         c         = refl
⊗ᶜ-assoc (cost m)  none      c         = refl
⊗ᶜ-assoc (cost m)  (cost n)  none      = refl
⊗ᶜ-assoc (cost m)  (cost n)  (cost k)  = cong cost (ℕₚ.+-assoc m n k)
⊗ᶜ-assoc (cost m)  (cost n)  unbounded = refl
⊗ᶜ-assoc (cost m)  unbounded none      = refl
⊗ᶜ-assoc (cost m)  unbounded (cost _)  = refl
⊗ᶜ-assoc (cost m)  unbounded unbounded = refl
⊗ᶜ-assoc unbounded none      c         = refl
⊗ᶜ-assoc unbounded (cost n)  none      = refl
⊗ᶜ-assoc unbounded (cost n)  (cost _)  = refl
⊗ᶜ-assoc unbounded (cost n)  unbounded = refl
⊗ᶜ-assoc unbounded unbounded none      = refl
⊗ᶜ-assoc unbounded unbounded (cost _)  = refl
⊗ᶜ-assoc unbounded unbounded unbounded = refl

⊗ᶜ-zeroʳ : ∀ a → a ⊗ᶜ none ≡ none
⊗ᶜ-zeroʳ none      = refl
⊗ᶜ-zeroʳ (cost _)  = refl
⊗ᶜ-zeroʳ unbounded = refl

⊗ᶜ-distribˡ : ∀ a b c → a ⊗ᶜ (b ⊕ᶜ c) ≤ᶜ (a ⊗ᶜ b) ⊕ᶜ (a ⊗ᶜ c)
⊗ᶜ-distribˡ a b c =
  ≤ᶜ-trans (lemma a b c) ≤ᶜ-refl
  where
    lemma : ∀ a b c → a ⊗ᶜ (b ⊕ᶜ c) ≤ᶜ (a ⊗ᶜ b) ⊕ᶜ (a ⊗ᶜ c)
    lemma none      b c = none≤
    lemma (cost m)  none c = ⊕ᶜ-ubʳ none _
    lemma (cost m)  (cost n) none = ≤ᶜ-refl
    lemma (cost m)  (cost n) (cost k) = cost≤ (ℕₚ.≤-reflexive (ℕₚ.+-distribˡ-⊔ m n k))
    lemma (cost m)  (cost n) unbounded = unb≤unb
    lemma (cost m)  unbounded c = unb≤unb
    lemma unbounded none c = ⊕ᶜ-ubʳ none _
    lemma unbounded (cost n) none = unb≤unb
    lemma unbounded (cost n) (cost _) = unb≤unb
    lemma unbounded (cost n) unbounded = unb≤unb
    lemma unbounded unbounded c = unb≤unb

⊗ᶜ-comm : ∀ a b → a ⊗ᶜ b ≡ b ⊗ᶜ a
⊗ᶜ-comm none      none      = refl
⊗ᶜ-comm none      (cost _)  = refl
⊗ᶜ-comm none      unbounded = refl
⊗ᶜ-comm (cost _)  none      = refl
⊗ᶜ-comm (cost m)  (cost n)  = cong cost (ℕₚ.+-comm m n)
⊗ᶜ-comm (cost _)  unbounded = refl
⊗ᶜ-comm unbounded none      = refl
⊗ᶜ-comm unbounded (cost _)  = refl
⊗ᶜ-comm unbounded unbounded = refl

⊕ᶜ-comm : ∀ a b → a ⊕ᶜ b ≤ᶜ b ⊕ᶜ a
⊕ᶜ-comm a b = ⊕ᶜ-lub (⊕ᶜ-ubʳ b a) (⊕ᶜ-ubˡ b a)

costs : Dioid
costs = record
  { Carrier      = Cost
  ; _≤_          = _≤ᶜ_
  ; 𝟘            = none
  ; 𝟙            = cost 0
  ; ⊤            = unbounded
  ; _⊕_          = _⊕ᶜ_
  ; _⊗_          = _⊗ᶜ_
  ; ≤-refl       = ≤ᶜ-refl
  ; ≤-trans      = ≤ᶜ-trans
  ; ≤-irrelevant = ≤ᶜ-irrelevant
  ; _≤?_         = _≤ᶜ?_
  ; 𝟘-≤          = λ _ → none≤
  ; ≤-⊤          = ≤ᶜ-unb
  ; ⊕-ubˡ        = ⊕ᶜ-ubˡ
  ; ⊕-ubʳ        = ⊕ᶜ-ubʳ
  ; ⊕-lub        = ⊕ᶜ-lub
  ; ⊗-identityˡ  = λ a → ≡⇒≈ (⊗ᶜ-identityˡ a)
  ; ⊗-identityʳ  = λ a → ≡⇒≈ (⊗ᶜ-identityʳ a)
  ; ⊗-assoc      = λ a b c → ≡⇒≈ (⊗ᶜ-assoc a b c)
  ; ⊗-mono       = ⊗ᶜ-mono
  ; ⊗-zeroˡ      = λ _ → none≤
  ; ⊗-zeroʳ      = λ a → ≤ᶜ-trans (proj₁ (≡⇒≈ (⊗ᶜ-zeroʳ a))) none≤
  ; ⊗-distribˡ   = ⊗ᶜ-distribˡ
  ; ⊗-distribʳ   = λ a b c →
      ≤ᶜ-trans (proj₁ (≡⇒≈ (⊗ᶜ-comm (b ⊕ᶜ c) a)))
        (≤ᶜ-trans (⊗ᶜ-distribˡ a b c)
          (⊕ᶜ-lub (≤ᶜ-trans (proj₁ (≡⇒≈ (⊗ᶜ-comm a b))) (⊕ᶜ-ubˡ _ _))
                  (≤ᶜ-trans (proj₁ (≡⇒≈ (⊗ᶜ-comm a c))) (⊕ᶜ-ubʳ _ _))))
  }

------------------------------------------------------------------------
-- The conditions of mode matrices: a change costs at least 1

Change : Cost → Set
Change c = (c ≤ᶜ none) ⊎ (cost 1 ≤ᶜ c)

private
  -- a product with a change is a change
  change-⊗ : ∀ {a} b → cost 1 ≤ᶜ a → Change (a ⊗ᶜ b)
  change-⊗ none      (cost≤ _) = inj₁ none≤
  change-⊗ (cost n)  (cost≤ p) = inj₂ (cost≤ (ℕₚ.≤-trans p (ℕₚ.m≤m+n _ n)))
  change-⊗ unbounded (cost≤ _) = inj₂ cost≤unb
  change-⊗ none      cost≤unb  = inj₁ none≤
  change-⊗ (cost _)  cost≤unb  = inj₂ cost≤unb
  change-⊗ unbounded cost≤unb  = inj₂ cost≤unb

  no-zero-divisors : ∀ {a b} → a ⊗ᶜ b ≤ᶜ none → (a ≤ᶜ none) ⊎ (b ≤ᶜ none)
  no-zero-divisors {none}      _ = inj₁ none≤
  no-zero-divisors {cost _}    {none}      _ = inj₂ none≤
  no-zero-divisors {unbounded} {none}      _ = inj₂ none≤
  no-zero-divisors {cost _}    {cost _}    ()
  no-zero-divisors {cost _}    {unbounded} ()
  no-zero-divisors {unbounded} {cost _}    ()
  no-zero-divisors {unbounded} {unbounded} ()

  unit-reflects : ∀ {a b} → a ⊗ᶜ b ≤ᶜ cost 0 → ¬ (a ≤ᶜ none) → ¬ (b ≤ᶜ none)
                → (a ≤ᶜ cost 0) × (b ≤ᶜ cost 0)
  unit-reflects {none}      _ a≰ _ = ⊥-elim (a≰ none≤)
  unit-reflects {cost _}    {none}      _ _ b≰ = ⊥-elim (b≰ none≤)
  unit-reflects {unbounded} {none}      _ _ b≰ = ⊥-elim (b≰ none≤)
  unit-reflects {cost m}    {cost n}    (cost≤ p) _ _ =
    cost≤ (ℕₚ.≤-trans (ℕₚ.m≤m+n m n) p) , cost≤ (ℕₚ.≤-trans (ℕₚ.m≤n+m n m) p)
  unit-reflects {cost _}    {unbounded} () _ _
  unit-reflects {unbounded} {cost _}    () _ _
  unit-reflects {unbounded} {unbounded} () _ _

open import Grades.Matrix.Nominal ℕ-infinite using (trivial)
open import Grades.Matrix.ModeGrade ℕ-infinite costs (trivial costs)

cost-entries : ModeEntries
cost-entries = record
  { nontrivial       = λ ()
  ; no-zero-divisors = no-zero-divisors
  ; unit-reflects     = unit-reflects
  ; Change           = Change
  ; change-𝟘         = inj₁
  ; change-⊤         = inj₂ cost≤unb
  ; change-≈         = λ { (_ , b≤a) (inj₁ a≤) → inj₁ (≤ᶜ-trans b≤a a≤)
                         ; (a≤b , _) (inj₂ 1≤a) → inj₂ (≤ᶜ-trans 1≤a a≤b) }
  ; change-⊕         = λ { {a} {b} (inj₁ p) (inj₁ q) → inj₁ (⊕ᶜ-lub p q)
                         ; {a} {b} (inj₂ p) _        → inj₂ (≤ᶜ-trans p (⊕ᶜ-ubˡ a b))
                         ; {a} {b} (inj₁ _) (inj₂ q) → inj₂ (≤ᶜ-trans q (⊕ᶜ-ubʳ a b)) }
  ; change-⊗ˡ        = λ { {a} {b} (inj₁ p) → inj₁ (⊗ᶜ-mono p (≤ᶜ-refl {b}))
                         ; {a} {b} (inj₂ p) → change-⊗ b p }
  ; change-⊗ʳ        = λ { {a} {b} (inj₁ p) →
                             inj₁ (≤ᶜ-trans (⊗ᶜ-mono (≤ᶜ-refl {a}) p) (≤ᶜ-trans (≤ᶜ-reflexive (⊗ᶜ-zeroʳ a)) none≤))
                         ; {a} {b} (inj₂ p) → subst Change (⊗ᶜ-comm b a) (change-⊗ a p) }
  ; change-not-unit  = not-unit
  ; change-act       = λ c → c
  ; change-orbit     = λ c → c
  }
  where
    ≤ᶜ-reflexive : ∀ {a b} → a ≡ b → a ≤ᶜ b
    ≤ᶜ-reflexive refl = ≤ᶜ-refl
    not-unit : ∀ {a b} → Change a → ¬ (a ≤ᶜ none) → ¬ (b ≤ᶜ none) → ¬ (a ⊗ᶜ b ≤ᶜ cost 0)
    not-unit (inj₁ a≤) a≰ _ _ = a≰ a≤
    not-unit {a} {b} (inj₂ p) a≰ b≰ ab with change-⊗ b p
    ... | inj₁ z with no-zero-divisors {a} {b} z
    ...   | inj₁ a≤ = a≰ a≤
    ...   | inj₂ b≤ = b≰ b≤
    not-unit {a} {b} (inj₂ p) a≰ b≰ ab | inj₂ q with ≤ᶜ-trans q ab
    ... | cost≤ ()

change? : ∀ a → Dec (Change a)
change? a = (a ≤ᶜ? none) ⊎-dec (cost 1 ≤ᶜ? a)

------------------------------------------------------------------------
-- The grade

mode-switch-costs : {D : Duration} → Grade D
mode-switch-costs = mode-grade cost-entries

open Decided cost-entries change? public using (decided)
open import Grades.Matrix.Matrices ℕ-infinite costs (trivial costs) public
  using (Matrix; entry)
open import Grades.Matrix.Fields ℕ-infinite costs using (fields; fromFields)
open import Grades.Matrix.Modes ℕ-infinite public using (Mode; stuck; ⌜_⌝)

------------------------------------------------------------------------
-- Literals

-- a mode named, one not named, another not named, and `stuck`

data Point : Set where
  ⟨_⟩ : ℕ → Point
  ⋆ ⋆' ✗ : Point

_==_ : Point → Point → Bool
⟨ m ⟩ == ⟨ n ⟩ = m ≡ᵇ n
⋆     == ⋆     = true
⋆'    == ⋆'    = true
✗     == ✗     = true
_     == _     = false

Entry : Set
Entry = Point × Point × Cost

private
  find : List Entry → Point → Point → Cost → Cost
  find []                 x y d = d
  find ((x' , y' , c) ∷ es) x y d = if (x == x') ∧' (y == y') then c else find es x y d
    where
      _∧'_ : Bool → Bool → Bool
      true  ∧' b = b
      false ∧' _ = false

  starts : List Entry → Point → Bool
  starts []                 x = false
  starts ((x' , _ , _) ∷ es) x = (x == x') ∨ starts es x

  names : List Entry → List ℕ
  names = concatMap λ { (x , y , _) → name x ++ᴸ name y }
    where
      name : Point → List ℕ
      name ⟨ n ⟩ = n ∷ []
      name _     = []
      _++ᴸ_ : List ℕ → List ℕ → List ℕ
      []       ++ᴸ ys = ys
      (x ∷ xs) ++ᴸ ys = x ∷ (xs ++ᴸ ys)

  -- into `stuck`: as listed, or at cost 0 from a mode no entry starts
  -- from
  into-stuck : List Entry → Point → Cost
  into-stuck es x = find es x ✗ (if starts es x then none else cost 0)

-- the matrix of a list of entries, the others having no trace

listing : List Entry → Matrix
listing es = fromFields $ fields (names es)
  (λ p q → find es ⟨ p ⟩ ⟨ q ⟩ none) (λ p → find es ⟨ p ⟩ ⋆ none)
  (λ q → find es ⋆ ⟨ q ⟩ none) (λ p → into-stuck es ⟨ p ⟩)
  (find es ⋆ ⋆ none) (find es ⋆ ⋆' none) (into-stuck es ⋆)

-- the entries of a grade

entryᵐ : Grade.Carrier (mode-switch-costs {ℕᴰ}) → Mode → Mode → Cost
entryᵐ x = entry (ModeMatrix.mat x)
