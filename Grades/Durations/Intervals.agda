------------------------------------------------------------------------
-- Intervals of a time domain, with open or closed ends.               --
--                                                                    --
-- An end is a cut of the time domain: a point `p` with a side,        --
-- `p ∣ ⁻` lying just below `p` and `p ∣ ⁺` just above it, the cuts    --
-- ordered lexicographically (`_⊑_`). A lower end `c` admits the       --
-- durations above it -- `p ∣ ⁻` is "at least p", `p ∣ ⁺` "more than  --
-- p" -- and an upper end, a cut or `∞`, admits those below it --      --
-- `p ∣ ⁺` is "at most p", `p ∣ ⁻` "less than p".                      --
--                                                                    --
-- Ends add pointwise, an end of a sum being open exactly when an end  --
-- summed is: on lower ends that takes the larger side, on upper ends  --
-- the smaller, so the two kinds of end are two monoids. An interval   --
-- is a lower and an upper end, the lower strictly below the upper.    --
-- Intervals are ordered by their ends (`_⊆ⁱ_`), the lower end         --
-- reversed, summed end by end (`_⊕_`), and joined by the hull         --
-- (`_∪ⁱ_`), with the laws a grade asks for; the grade itself is      --
-- `Grades.Examples.Time.Intervals`.                                  --
--                                                                    --
-- A lower end admits durations from `inf`, an upper cut up to `sup`: --
-- the point of the end, or, at an open end in a discrete time domain, --
-- the adjacent step.                                                 --
--                                                                    --
-- What the ends say about the durations admitted (`_∈ⁱ_`) -- that    --
-- the order is containment and the sum the Minkowski sum, in a dense --
-- time domain -- is in `Durations.Intervals.Dense`.                  --
------------------------------------------------------------------------

open import Grades.Durations

module Grades.Durations.Intervals {D : Duration} (T : TimeDomain D) where

open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool.Properties using (T-irrelevant)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core
  using (True; toWitness; fromWitness)

open import Util.Equality

open import Grades.Durations.Monus T

------------------------------------------------------------------------
-- Sides

data Side : Set where
  ⁻ ⁺ : Side

infix 4 _≤ˢ_

data _≤ˢ_ : Side → Side → Set where
  ⁻≤  : ∀ {s} → ⁻ ≤ˢ s
  ⁺≤⁺ : ⁺ ≤ˢ ⁺

_≤ˢ?_ : Decidable _≤ˢ_
⁻ ≤ˢ? _ = yes ⁻≤
⁺ ≤ˢ? ⁻ = no λ ()
⁺ ≤ˢ? ⁺ = yes ⁺≤⁺

≤ˢ-refl : ∀ {s} → s ≤ˢ s
≤ˢ-refl {⁻} = ⁻≤
≤ˢ-refl {⁺} = ⁺≤⁺

≤ˢ-⁺ : ∀ {s} → s ≤ˢ ⁺
≤ˢ-⁺ {⁻} = ⁻≤
≤ˢ-⁺ {⁺} = ⁺≤⁺

≤ˢ-trans : ∀ {s s' s''} → s ≤ˢ s' → s' ≤ˢ s'' → s ≤ˢ s''
≤ˢ-trans ⁻≤  _   = ⁻≤
≤ˢ-trans ⁺≤⁺ ⁺≤⁺ = ⁺≤⁺

≤ˢ-antisym : ∀ {s s'} → s ≤ˢ s' → s' ≤ˢ s → s ≡ s'
≤ˢ-antisym {⁻} {⁻} _ _ = refl
≤ˢ-antisym {⁺} {⁺} _ _ = refl
≤ˢ-antisym {⁻} {⁺} _ ()

≤ˢ-total : ∀ s s' → s ≤ˢ s' ⊎ s' ≤ˢ s
≤ˢ-total ⁻ _ = inj₁ ⁻≤
≤ˢ-total ⁺ ⁻ = inj₂ ⁻≤
≤ˢ-total ⁺ ⁺ = inj₁ ⁺≤⁺

-- the larger and the smaller side

infixl 7 _∨ˢ_ _∧ˢ_

_∨ˢ_ : Side → Side → Side
⁻ ∨ˢ s = s
⁺ ∨ˢ _ = ⁺

_∧ˢ_ : Side → Side → Side
⁻ ∧ˢ _ = ⁻
⁺ ∧ˢ s = s

∨ˢ-comm : ∀ s s' → s ∨ˢ s' ≡ s' ∨ˢ s
∨ˢ-comm ⁻ ⁻ = refl
∨ˢ-comm ⁻ ⁺ = refl
∨ˢ-comm ⁺ ⁻ = refl
∨ˢ-comm ⁺ ⁺ = refl

∧ˢ-comm : ∀ s s' → s ∧ˢ s' ≡ s' ∧ˢ s
∧ˢ-comm ⁻ ⁻ = refl
∧ˢ-comm ⁻ ⁺ = refl
∧ˢ-comm ⁺ ⁻ = refl
∧ˢ-comm ⁺ ⁺ = refl

∨ˢ-assoc : ∀ s s' s'' → (s ∨ˢ s') ∨ˢ s'' ≡ s ∨ˢ (s' ∨ˢ s'')
∨ˢ-assoc ⁻ _ _ = refl
∨ˢ-assoc ⁺ _ _ = refl

∧ˢ-assoc : ∀ s s' s'' → (s ∧ˢ s') ∧ˢ s'' ≡ s ∧ˢ (s' ∧ˢ s'')
∧ˢ-assoc ⁻ _ _ = refl
∧ˢ-assoc ⁺ _ _ = refl

∨ˢ-identityʳ : ∀ s → s ∨ˢ ⁻ ≡ s
∨ˢ-identityʳ ⁻ = refl
∨ˢ-identityʳ ⁺ = refl

∧ˢ-identityʳ : ∀ s → s ∧ˢ ⁺ ≡ s
∧ˢ-identityʳ ⁻ = refl
∧ˢ-identityʳ ⁺ = refl

∨ˢ-ubʳ : ∀ s s' → s' ≤ˢ s ∨ˢ s'
∨ˢ-ubʳ ⁻ _ = ≤ˢ-refl
∨ˢ-ubʳ ⁺ _ = ≤ˢ-⁺

∨ˢ-monoˡ : ∀ {s s'} t → s ≤ˢ s' → s ∨ˢ t ≤ˢ s' ∨ˢ t
∨ˢ-monoˡ {s' = s'} t ⁻≤ = ∨ˢ-ubʳ s' t
∨ˢ-monoˡ t ⁺≤⁺ = ≤ˢ-refl

∧ˢ-monoˡ : ∀ {s s'} t → s ≤ˢ s' → s ∧ˢ t ≤ˢ s' ∧ˢ t
∧ˢ-monoˡ t ⁻≤  = ⁻≤
∧ˢ-monoˡ t ⁺≤⁺ = ≤ˢ-refl

-- a join at ⁻ has both sides ⁻, a meet at ⁺ both sides ⁺

∨ˢ-⁻ˡ : ∀ {s s'} → s ∨ˢ s' ≡ ⁻ → s ≡ ⁻
∨ˢ-⁻ˡ {⁻} _ = refl

∨ˢ-⁻ʳ : ∀ {s s'} → s ∨ˢ s' ≡ ⁻ → s' ≡ ⁻
∨ˢ-⁻ʳ {⁻} e = e

∧ˢ-⁺ˡ : ∀ {s s'} → s ∧ˢ s' ≡ ⁺ → s ≡ ⁺
∧ˢ-⁺ˡ {⁺} _ = refl

∧ˢ-⁺ʳ : ∀ {s s'} → s ∧ˢ s' ≡ ⁺ → s' ≡ ⁺
∧ˢ-⁺ʳ {⁺} e = e

------------------------------------------------------------------------
-- Cuts

infix 8 _∣_

record Cut : Set where
  constructor _∣_
  field
    pt   : Carrier
    side : Side

open Cut public

-- the lexicographic order

infix 4 _⊑_ _⊏_ _⊑?_

data _⊑_ (c c' : Cut) : Set where
  by-pt   : .(pt c <ᴰ pt c') → c ⊑ c'
  by-side : pt c ≡ pt c' → side c ≤ˢ side c' → c ⊑ c'

_⊑?_ : Decidable _⊑_
c ⊑? c' with compare (pt c) (pt c')
... | tri< p = yes (by-pt p)
... | tri> p = no λ { (by-pt q) → ⊥-elim-irr (<-irrefl (<-trans p q))
                    ; (by-side e _) → <⇒≢ p (sym e) }
... | tri≈ e with side c ≤ˢ? side c'
...   | yes q = yes (by-side e q)
...   | no ¬q = no λ { (by-pt p) → ⊥-elim-irr (<⇒≢ p e) ; (by-side _ q) → ¬q q }

⊑-refl : ∀ {c} → c ⊑ c
⊑-refl = by-side refl ≤ˢ-refl

⊑-reflexive : ∀ {c c'} → c ≡ c' → c ⊑ c'
⊑-reflexive refl = ⊑-refl

⊑-trans : ∀ {c c' c''} → c ⊑ c' → c' ⊑ c'' → c ⊑ c''
⊑-trans (by-pt p)      (by-pt q)       = by-pt (<-trans p q)
⊑-trans (by-pt p)      (by-side e _)   = by-pt (subst (_ <ᴰ_) e p)
⊑-trans (by-side e _)  (by-pt q)       = by-pt (subst (_<ᴰ _) (sym e) q)
⊑-trans (by-side e q)  (by-side e' q') = by-side (trans e e') (≤ˢ-trans q q')

⊑-antisym : ∀ {c c'} → c ⊑ c' → c' ⊑ c → c ≡ c'
⊑-antisym (by-pt p)     (by-pt q)      = ⊥-elim-irr (<-irrefl (<-trans p q))
⊑-antisym (by-pt p)     (by-side e _)  = ⊥-elim-irr (<⇒≢ p (sym e))
⊑-antisym (by-side e _) (by-pt q)      = ⊥-elim-irr (<⇒≢ q (sym e))
⊑-antisym (by-side e q) (by-side _ q') = cong₂ _∣_ e (≤ˢ-antisym q q')

≤ˢ-irrelevant : ∀ {s s'} (p q : s ≤ˢ s') → p ≡ q
≤ˢ-irrelevant ⁻≤  ⁻≤  = refl
≤ˢ-irrelevant ⁺≤⁺ ⁺≤⁺ = refl

⊑-irrelevant : ∀ {c c'} (p q : c ⊑ c') → p ≡ q
⊑-irrelevant (by-pt _)     (by-pt _)      = refl
⊑-irrelevant (by-pt p)     (by-side e _)  = ⊥-elim-irr (<⇒≢ p e)
⊑-irrelevant (by-side e _) (by-pt p)      = ⊥-elim-irr (<⇒≢ p e)
⊑-irrelevant (by-side e q) (by-side e' q') =
  cong₂ by-side uip (≤ˢ-irrelevant q q')

⊑-total : ∀ c c' → c ⊑ c' ⊎ c' ⊑ c
⊑-total c c' with compare (pt c) (pt c')
... | tri< p = inj₁ (by-pt p)
... | tri> p = inj₂ (by-pt p)
... | tri≈ e with ≤ˢ-total (side c) (side c')
...   | inj₁ q = inj₁ (by-side e q)
...   | inj₂ q = inj₂ (by-side (sym e) q)

-- comparing cuts compares their points

⊑⇒≤ : ∀ {c c'} → c ⊑ c' → pt c ≤ᴰ pt c'
⊑⇒≤ {c} {c'} (by-pt a) with pt c ≤ᴰ? pt c'
... | yes b = b
... | no ¬b = ⊥-elim-irr (a (<⇒≤ ¬b))
⊑⇒≤ (by-side e _) = ≤ᴰ-reflexive e

-- and cuts on the same side of two points compare as the points do

≤⇒⁻⊑⁻ : ∀ {q r} → q ≤ᴰ r → (q ∣ ⁻) ⊑ (r ∣ ⁻)
≤⇒⁻⊑⁻ {q} {r} b with compare q r
... | tri< a = by-pt a
... | tri≈ e = by-side e ⁻≤
... | tri> a = ⊥-elim (a b)

≤⇒⁺⊑⁺ : ∀ {q r} → q ≤ᴰ r → (q ∣ ⁺) ⊑ (r ∣ ⁺)
≤⇒⁺⊑⁺ {q} {r} b with compare q r
... | tri< a = by-pt a
... | tri≈ e = by-side e ⁺≤⁺
... | tri> a = ⊥-elim (a b)

-- the strict order

_⊏_ : Cut → Cut → Set
c ⊏ c' = ¬ (c' ⊑ c)

⊏⇒⊑ : ∀ {c c'} → c ⊏ c' → c ⊑ c'
⊏⇒⊑ {c} {c'} p with ⊑-total c c'
... | inj₁ q = q
... | inj₂ q = ⊥-elim (p q)

⊏-⊑-trans : ∀ {c c' c''} → c ⊏ c' → c' ⊑ c'' → c ⊏ c''
⊏-⊑-trans p q r = p (⊑-trans q r)

⊑-⊏-trans : ∀ {c c' c''} → c ⊑ c' → c' ⊏ c'' → c ⊏ c''
⊑-⊏-trans p q r = q (⊑-trans r p)

-- a strict comparison: a smaller point, or the two sides of one point

⊏-by-pt : ∀ {c c'} → pt c <ᴰ pt c' → c ⊏ c'
⊏-by-pt p (by-pt q)      = ⊥-elim-irr (<-irrefl (<-trans p q))
⊏-by-pt p (by-side e _)  = <⇒≢ p (sym e)

⊏-by-side : ∀ {p q} → p ≡ q → (p ∣ ⁻) ⊏ (q ∣ ⁺)
⊏-by-side e (by-pt r)     = ⊥-elim-irr (<⇒≢ r (sym e))
⊏-by-side e (by-side _ ())

⊏-cases : ∀ {c c'} → c ⊏ c'
        → pt c <ᴰ pt c' ⊎ (pt c ≡ pt c' × side c ≡ ⁻ × side c' ≡ ⁺)
⊏-cases {p ∣ s} {q ∣ t} r with compare p q
... | tri< a = inj₁ a
... | tri> a = ⊥-elim (r (by-pt a))
... | tri≈ e with s | t
...   | ⁻ | ⁺ = inj₂ (e , refl , refl)
...   | ⁻ | ⁻ = ⊥-elim (r (by-side (sym e) ⁻≤))
...   | ⁺ | _ = ⊥-elim (r (by-side (sym e) ≤ˢ-⁺))

-- the least cut

0⁻ 0⁺ : Cut
0⁻ = 0ᴰ ∣ ⁻
0⁺ = 0ᴰ ∣ ⁺

0⁻-least : ∀ c → 0⁻ ⊑ c
0⁻-least (p ∣ s) with compare 0ᴰ p
... | tri< a = by-pt a
... | tri≈ e = by-side e ⁻≤
... | tri> a = ⊥-elim (a (0ᴰ-least p))

-- nothing lies strictly between `0 ∣ ⁻` and `0 ∣ ⁺`

0⁻⊏⇒0⁺⊑ : ∀ {c} → 0⁻ ⊏ c → 0⁺ ⊑ c
0⁻⊏⇒0⁺⊑ {p ∣ s} r with ⊏-cases r
... | inj₁ a              = by-pt a
... | inj₂ (e , _ , refl) = by-side e ⁺≤⁺

-- the extreme durations an end admits: a lower end `c` admits at
-- least `inf c`, and an upper cut `c` at most `sup c`. An open end
-- moves a step inward in a discrete time domain, and stays at its
-- point in a dense one, where it is the infimum or supremum of what
-- the end admits

closeˡ closeʰ : Carrier → Cut → Carrier
closeˡ ε (p ∣ ⁻) = p
closeˡ ε (p ∣ ⁺) = ε +ᴰ p
closeʰ ε (q ∣ ⁺) = q
closeʰ ε (q ∣ ⁻) = q ∸ᴰ ε

inf sup : Cut → Carrier
inf c with grain
... | dense _        = pt c
... | discrete ε _ _ = closeˡ ε c
sup c with grain
... | dense _        = pt c
... | discrete ε _ _ = closeʰ ε c

-- the grain, as a proposition

dense-or-discrete : Dense T ⊎ Discrete T
dense-or-discrete with grain
... | dense d                  = inj₁ d
... | discrete ε ε-pos ε-least = inj₂ (ε , ε-pos , ε-least)

-- in a dense time domain they are the points of the ends

inf-dense : Dense T → ∀ c → inf c ≡ pt c
inf-dense d c with grain
... | dense _              = refl
... | discrete ε ε-pos ε-least = ⊥-elim (dense-discrete {T = T} d (ε , ε-pos , ε-least))

sup-dense : Dense T → ∀ c → sup c ≡ pt c
sup-dense d c with grain
... | dense _              = refl
... | discrete ε ε-pos ε-least = ⊥-elim (dense-discrete {T = T} d (ε , ε-pos , ε-least))

private
  ⁺⊑⁻⇒< : ∀ {p q} → (p ∣ ⁺) ⊑ (q ∣ ⁻) → p <ᴰ q
  ⁺⊑⁻⇒< {p} {q} r with q ≤ᴰ? p
  ... | no ¬b = ¬b
  ⁺⊑⁻⇒< (by-pt a)      | yes b = ⊥-elim-irr (a b)
  ⁺⊑⁻⇒< (by-side _ ()) | yes b

  -- with a least positive duration `ε`, a step
  module Step (ε : Carrier) (ε-pos : 0ᴰ <ᴰ ε) (ε-least : ∀ τ → 0ᴰ <ᴰ τ → ε ≤ᴰ τ) where

    -- above a duration is at least a step above it
    <⇒step≤ : ∀ {p x} → p <ᴰ x → ε +ᴰ p ≤ᴰ x
    <⇒step≤ {p} {x} a with diff (<⇒≤ a)
    ... | κ , e = ≤ᴰ-trans (+ᴰ-monoˡ-≤ p (ε-least κ κ-pos))
                           (≤ᴰ-reflexive (trans (+ᴰ-comm κ p) e))
      where
        κ-pos : 0ᴰ <ᴰ κ
        κ-pos κ≤0 = a (≤ᴰ-reflexive
          (trans (sym e) (trans (cong (p +ᴰ_) (≤0⇒≡0 κ≤0)) (+ᴰ-identityʳ p))))

    -- below a duration is at least a step below it
    <⇒≤∸step : ∀ {x q} → x <ᴰ q → x ≤ᴰ q ∸ᴰ ε
    <⇒≤∸step {x} {q} a = +-≤-∸ (≤ᴰ-trans (≤ᴰ-+ ε x) (<⇒step≤ a)) (<⇒step≤ a)

    ∸step-< : ∀ {q} → ε ≤ᴰ q → q ∸ᴰ ε <ᴰ q
    ∸step-< {q} b = subst (q ∸ᴰ ε <ᴰ_) (∸-+ b) (<-+ ε-pos)

-- every duration a lower end admits is at least `inf`, and every
-- duration an upper cut admits at most `sup`

inf-≤ : ∀ {c x} → c ⊑ (x ∣ ⁻) → inf c ≤ᴰ x
inf-≤ {p ∣ ⁻} r with grain
... | dense _        = ⊑⇒≤ r
... | discrete _ _ _ = ⊑⇒≤ r
inf-≤ {p ∣ ⁺} r with grain
... | dense _                  = ⊑⇒≤ r
... | discrete ε ε-pos ε-least = Step.<⇒step≤ ε ε-pos ε-least (⁺⊑⁻⇒< r)

≤-sup : ∀ {c x} → (x ∣ ⁺) ⊑ c → x ≤ᴰ sup c
≤-sup {q ∣ ⁺} r with grain
... | dense _        = ⊑⇒≤ r
... | discrete _ _ _ = ⊑⇒≤ r
≤-sup {q ∣ ⁻} r with grain
... | dense _                  = ⊑⇒≤ r
... | discrete ε ε-pos ε-least = Step.<⇒≤∸step ε ε-pos ε-least (⁺⊑⁻⇒< r)

-- in a discrete time domain an end admits `inf` and `sup`, an upper cut
-- when it admits something

inf-admitted : Discrete T → ∀ c → c ⊑ (inf c ∣ ⁻)
inf-admitted δ (p ∣ ⁻) with grain
... | dense _        = ⊑-refl
... | discrete _ _ _ = ⊑-refl
inf-admitted δ (p ∣ ⁺) with grain
... | dense d            = ⊥-elim (dense-discrete {T = T} d δ)
... | discrete ε ε-pos _ = by-pt (<-+ˡ ε-pos)

sup-admitted : Discrete T → ∀ {c x} → (x ∣ ⁺) ⊑ c → (sup c ∣ ⁺) ⊑ c
sup-admitted δ {q ∣ ⁺} _ with grain
... | dense _        = ⊑-refl
... | discrete _ _ _ = ⊑-refl
sup-admitted δ {q ∣ ⁻} {x} r with grain
... | dense d                  = ⊥-elim (dense-discrete {T = T} d δ)
... | discrete ε ε-pos ε-least =
  by-pt (Step.∸step-< ε ε-pos ε-least
           (≤ᴰ-trans (≤ᴰ-+ ε x) (Step.<⇒step≤ ε ε-pos ε-least (⁺⊑⁻⇒< r))))

-- the smaller and the larger cut

infixl 7 _⊓ᶜ_ _⊔ᶜ_

_⊓ᶜ_ : Cut → Cut → Cut
c ⊓ᶜ c' with c ⊑? c'
... | yes _ = c
... | no _  = c'

_⊔ᶜ_ : Cut → Cut → Cut
c ⊔ᶜ c' with c ⊑? c'
... | yes _ = c'
... | no _  = c

⊓ᶜ-lbˡ : ∀ c c' → c ⊓ᶜ c' ⊑ c
⊓ᶜ-lbˡ c c' with c ⊑? c'
... | yes _ = ⊑-refl
... | no ¬p = ⊏⇒⊑ ¬p

⊓ᶜ-lbʳ : ∀ c c' → c ⊓ᶜ c' ⊑ c'
⊓ᶜ-lbʳ c c' with c ⊑? c'
... | yes p = p
... | no _  = ⊑-refl

⊓ᶜ-glb : ∀ {c c' c''} → c'' ⊑ c → c'' ⊑ c' → c'' ⊑ c ⊓ᶜ c'
⊓ᶜ-glb {c} {c'} p q with c ⊑? c'
... | yes _ = p
... | no _  = q

⊓ᶜ-sel : ∀ c c' → c ⊓ᶜ c' ≡ c ⊎ c ⊓ᶜ c' ≡ c'
⊓ᶜ-sel c c' with c ⊑? c'
... | yes _ = inj₁ refl
... | no _  = inj₂ refl

⊔ᶜ-ubˡ : ∀ c c' → c ⊑ c ⊔ᶜ c'
⊔ᶜ-ubˡ c c' with c ⊑? c'
... | yes p = p
... | no _  = ⊑-refl

⊔ᶜ-ubʳ : ∀ c c' → c' ⊑ c ⊔ᶜ c'
⊔ᶜ-ubʳ c c' with c ⊑? c'
... | yes _ = ⊑-refl
... | no ¬p = ⊏⇒⊑ ¬p

⊔ᶜ-lub : ∀ {c c' c''} → c ⊑ c'' → c' ⊑ c'' → c ⊔ᶜ c' ⊑ c''
⊔ᶜ-lub {c} {c'} p q with c ⊑? c'
... | yes _ = q
... | no _  = p

⊔ᶜ-sel : ∀ c c' → c ⊔ᶜ c' ≡ c ⊎ c ⊔ᶜ c' ≡ c'
⊔ᶜ-sel c c' with c ⊑? c'
... | yes _ = inj₂ refl
... | no _  = inj₁ refl

-- on cuts at one side, they are the smaller and larger point

⊓ᶜ-⁻ : ∀ p q → (p ∣ ⁻) ⊓ᶜ (q ∣ ⁻) ≡ (p ⊓ᴰ q) ∣ ⁻
⊓ᶜ-⁻ p q = ⊑-antisym below (⊓ᶜ-glb (≤⇒⁻⊑⁻ (⊓-lbˡ p q)) (≤⇒⁻⊑⁻ (⊓-lbʳ p q)))
  where
    below : (p ∣ ⁻) ⊓ᶜ (q ∣ ⁻) ⊑ (p ⊓ᴰ q) ∣ ⁻
    below with ⊓ᶜ-sel (p ∣ ⁻) (q ∣ ⁻)
    ... | inj₁ e = subst (_⊑ (p ⊓ᴰ q) ∣ ⁻) (sym e)
                     (≤⇒⁻⊑⁻ (⊓-glb ≤ᴰ-refl
                       (⊑⇒≤ (subst (_⊑ q ∣ ⁻) e (⊓ᶜ-lbʳ (p ∣ ⁻) (q ∣ ⁻))))))
    ... | inj₂ e = subst (_⊑ (p ⊓ᴰ q) ∣ ⁻) (sym e)
                     (≤⇒⁻⊑⁻ (⊓-glb
                       (⊑⇒≤ (subst (_⊑ p ∣ ⁻) e (⊓ᶜ-lbˡ (p ∣ ⁻) (q ∣ ⁻)))) ≤ᴰ-refl))

⊔ᶜ-⁺ : ∀ p q → (p ∣ ⁺) ⊔ᶜ (q ∣ ⁺) ≡ (p ⊔ᴰ q) ∣ ⁺
⊔ᶜ-⁺ p q = ⊑-antisym (⊔ᶜ-lub (≤⇒⁺⊑⁺ (⊔-ubˡ p q)) (≤⇒⁺⊑⁺ (⊔-ubʳ p q))) above
  where
    above : (p ⊔ᴰ q) ∣ ⁺ ⊑ (p ∣ ⁺) ⊔ᶜ (q ∣ ⁺)
    above with ⊔ᶜ-sel (p ∣ ⁺) (q ∣ ⁺)
    ... | inj₁ e = subst ((p ⊔ᴰ q) ∣ ⁺ ⊑_) (sym e)
                     (≤⇒⁺⊑⁺ (⊔-lub ≤ᴰ-refl
                       (⊑⇒≤ (subst (q ∣ ⁺ ⊑_) e (⊔ᶜ-ubʳ (p ∣ ⁺) (q ∣ ⁺))))))
    ... | inj₂ e = subst ((p ⊔ᴰ q) ∣ ⁺ ⊑_) (sym e)
                     (≤⇒⁺⊑⁺ (⊔-lub
                       (⊑⇒≤ (subst (p ∣ ⁺ ⊑_) e (⊔ᶜ-ubˡ (p ∣ ⁺) (q ∣ ⁺)))) ≤ᴰ-refl))

-- sums of lower ends (the open side absorbing)

infixl 6 _+ˡ_

_+ˡ_ : Cut → Cut → Cut
(p ∣ s) +ˡ (q ∣ t) = (p +ᴰ q) ∣ (s ∨ˢ t)

+ˡ-identityˡ : ∀ c → 0⁻ +ˡ c ≡ c
+ˡ-identityˡ (p ∣ s) = cong (_∣ s) (+ᴰ-identityˡ p)

+ˡ-identityʳ : ∀ c → c +ˡ 0⁻ ≡ c
+ˡ-identityʳ (p ∣ s) = cong₂ _∣_ (+ᴰ-identityʳ p) (∨ˢ-identityʳ s)

+ˡ-assoc : ∀ c c' c'' → (c +ˡ c') +ˡ c'' ≡ c +ˡ (c' +ˡ c'')
+ˡ-assoc (p ∣ s) (q ∣ t) (r ∣ u) = cong₂ _∣_ (+ᴰ-assoc p q r) (∨ˢ-assoc s t u)

+ˡ-comm : ∀ c c' → c +ˡ c' ≡ c' +ˡ c
+ˡ-comm (p ∣ s) (q ∣ t) = cong₂ _∣_ (+ᴰ-comm p q) (∨ˢ-comm s t)

+ˡ-monoˡ : ∀ {c c'} d → c ⊑ c' → c +ˡ d ⊑ c' +ˡ d
+ˡ-monoˡ (q ∣ t) (by-pt a)     = by-pt (+ᴰ-monoˡ-< q a)
+ˡ-monoˡ (q ∣ t) (by-side e r) = by-side (cong (_+ᴰ q) e) (∨ˢ-monoˡ t r)

+ˡ-monoʳ : ∀ {c c'} d → c ⊑ c' → d +ˡ c ⊑ d +ˡ c'
+ˡ-monoʳ {c} {c'} d r =
  subst₂ _⊑_ (+ˡ-comm c d) (+ˡ-comm c' d) (+ˡ-monoˡ d r)

+ˡ-mono : ∀ {c c' d d'} → c ⊑ c' → d ⊑ d' → c +ˡ d ⊑ c' +ˡ d'
+ˡ-mono {c' = c'} {d = d} r r' = ⊑-trans (+ˡ-monoˡ d r) (+ˡ-monoʳ c' r')

-- a lower end grows by adding another

+ˡ-inflate : ∀ c c' → c ⊑ c +ˡ c'
+ˡ-inflate c c' =
  subst (_⊑ c +ˡ c') (+ˡ-identityʳ c) (+ˡ-monoʳ c (0⁻-least c'))

------------------------------------------------------------------------
-- Upper ends: a cut, or no bound

data Hi : Set where
  fin : Cut → Hi
  ∞   : Hi

infix 4 _⊑ʰ_ _⊑ʰ?_

_⊑ʰ_ : Hi → Hi → Set
fin c ⊑ʰ fin c' = c ⊑ c'
_     ⊑ʰ ∞      = ⊤
∞     ⊑ʰ fin _  = ⊥

_⊑ʰ?_ : Decidable _⊑ʰ_
fin c ⊑ʰ? fin c' = c ⊑? c'
fin _ ⊑ʰ? ∞      = yes tt
∞     ⊑ʰ? fin _  = no λ ()
∞     ⊑ʰ? ∞      = yes tt

⊑ʰ-refl : ∀ {h} → h ⊑ʰ h
⊑ʰ-refl {fin _} = ⊑-refl
⊑ʰ-refl {∞}     = tt

⊑ʰ-reflexive : ∀ {h h'} → h ≡ h' → h ⊑ʰ h'
⊑ʰ-reflexive refl = ⊑ʰ-refl

⊑ʰ-∞ : ∀ h → h ⊑ʰ ∞
⊑ʰ-∞ (fin _) = tt
⊑ʰ-∞ ∞       = tt

⊑ʰ-trans : ∀ {h h' h''} → h ⊑ʰ h' → h' ⊑ʰ h'' → h ⊑ʰ h''
⊑ʰ-trans {fin _} {fin _} {fin _} p q = ⊑-trans p q
⊑ʰ-trans {fin _} {_}     {∞}     _ _ = tt
⊑ʰ-trans {fin _} {∞}     {fin _} _ ()
⊑ʰ-trans {∞}     {∞}     {∞}     _ _ = tt
⊑ʰ-trans {∞}     {fin _} {_}     () _
⊑ʰ-trans {∞}     {∞}     {fin _} _ ()

⊑ʰ-irrelevant : ∀ {h h'} (p q : h ⊑ʰ h') → p ≡ q
⊑ʰ-irrelevant {fin _} {fin _} p q = ⊑-irrelevant p q
⊑ʰ-irrelevant {fin _} {∞}     _ _ = refl
⊑ʰ-irrelevant {∞}     {∞}     _ _ = refl
⊑ʰ-irrelevant {∞}     {fin _} () _

⊑ʰ-antisym : ∀ {h h'} → h ⊑ʰ h' → h' ⊑ʰ h → h ≡ h'
⊑ʰ-antisym {fin _} {fin _} p q = cong fin (⊑-antisym p q)
⊑ʰ-antisym {fin _} {∞}     _ ()
⊑ʰ-antisym {∞}     {fin _} () _
⊑ʰ-antisym {∞}     {∞}     _ _ = refl

-- the larger upper end

infixl 7 _⊔ʰ_

_⊔ʰ_ : Hi → Hi → Hi
fin c ⊔ʰ fin c' = fin (c ⊔ᶜ c')
fin _ ⊔ʰ ∞      = ∞
∞     ⊔ʰ _      = ∞

⊔ʰ-ubˡ : ∀ h h' → h ⊑ʰ h ⊔ʰ h'
⊔ʰ-ubˡ (fin c) (fin c') = ⊔ᶜ-ubˡ c c'
⊔ʰ-ubˡ (fin _) ∞        = tt
⊔ʰ-ubˡ ∞       _        = tt

⊔ʰ-ubʳ : ∀ h h' → h' ⊑ʰ h ⊔ʰ h'
⊔ʰ-ubʳ (fin c) (fin c') = ⊔ᶜ-ubʳ c c'
⊔ʰ-ubʳ (fin _) ∞        = tt
⊔ʰ-ubʳ ∞       h'       = ⊑ʰ-∞ h'

⊔ʰ-lub : ∀ {h h' h''} → h ⊑ʰ h'' → h' ⊑ʰ h'' → h ⊔ʰ h' ⊑ʰ h''
⊔ʰ-lub {fin _} {fin _} {fin _} p q = ⊔ᶜ-lub p q
⊔ʰ-lub {fin _} {∞}     {fin _} _ ()
⊔ʰ-lub {∞}     {_}     {fin _} () _
⊔ʰ-lub {_}     {_}     {∞}     _ _ = ⊑ʰ-∞ _

⊔ʰ-sel : ∀ h h' → h ⊔ʰ h' ≡ h ⊎ h ⊔ʰ h' ≡ h'
⊔ʰ-sel (fin c) (fin c') with ⊔ᶜ-sel c c'
... | inj₁ e = inj₁ (cong fin e)
... | inj₂ e = inj₂ (cong fin e)
⊔ʰ-sel (fin _) ∞ = inj₂ refl
⊔ʰ-sel ∞       _ = inj₁ refl

-- sums of upper ends (the open side absorbing, and no bound absorbing)

infixl 6 _+ʰ_

_+ʰ_ : Hi → Hi → Hi
fin (p ∣ s) +ʰ fin (q ∣ t) = fin ((p +ᴰ q) ∣ (s ∧ˢ t))
fin _       +ʰ ∞           = ∞
∞           +ʰ _           = ∞

+ʰ-identityˡ : ∀ h → fin 0⁺ +ʰ h ≡ h
+ʰ-identityˡ (fin (p ∣ s)) = cong (λ x → fin (x ∣ s)) (+ᴰ-identityˡ p)
+ʰ-identityˡ ∞             = refl

+ʰ-identityʳ : ∀ h → h +ʰ fin 0⁺ ≡ h
+ʰ-identityʳ (fin (p ∣ s)) = cong fin (cong₂ _∣_ (+ᴰ-identityʳ p) (∧ˢ-identityʳ s))
+ʰ-identityʳ ∞             = refl

+ʰ-assoc : ∀ h h' h'' → (h +ʰ h') +ʰ h'' ≡ h +ʰ (h' +ʰ h'')
+ʰ-assoc (fin (p ∣ s)) (fin (q ∣ t)) (fin (r ∣ u)) =
  cong fin (cong₂ _∣_ (+ᴰ-assoc p q r) (∧ˢ-assoc s t u))
+ʰ-assoc (fin _) (fin _) ∞ = refl
+ʰ-assoc (fin _) ∞       _ = refl
+ʰ-assoc ∞       _       _ = refl

+ʰ-comm : ∀ h h' → h +ʰ h' ≡ h' +ʰ h
+ʰ-comm (fin (p ∣ s)) (fin (q ∣ t)) = cong fin (cong₂ _∣_ (+ᴰ-comm p q) (∧ˢ-comm s t))
+ʰ-comm (fin _) ∞       = refl
+ʰ-comm ∞       (fin _) = refl
+ʰ-comm ∞       ∞       = refl

+ʰ-∞ : ∀ h → h +ʰ ∞ ≡ ∞
+ʰ-∞ (fin (_ ∣ _)) = refl
+ʰ-∞ ∞             = refl

+ʰ-monoˡ : ∀ {h h'} k → h ⊑ʰ h' → h +ʰ k ⊑ʰ h' +ʰ k
+ʰ-monoˡ {h} {h'} ∞ _ rewrite +ʰ-∞ h | +ʰ-∞ h' = tt
+ʰ-monoˡ {fin _} {fin _} (fin (q ∣ t)) (by-pt a)     = by-pt (+ᴰ-monoˡ-< q a)
+ʰ-monoˡ {fin _} {fin _} (fin (q ∣ t)) (by-side e r) =
  by-side (cong (_+ᴰ q) e) (∧ˢ-monoˡ t r)
+ʰ-monoˡ {fin (_ ∣ _)} {∞} (fin (_ ∣ _)) _ = tt
+ʰ-monoˡ {∞}     {∞}     (fin _) _ = tt
+ʰ-monoˡ {∞}     {fin _} (fin _) ()

+ʰ-monoʳ : ∀ {h h'} k → h ⊑ʰ h' → k +ʰ h ⊑ʰ k +ʰ h'
+ʰ-monoʳ {h} {h'} k r =
  subst₂ _⊑ʰ_ (+ʰ-comm h k) (+ʰ-comm h' k) (+ʰ-monoˡ k r)

+ʰ-mono : ∀ {h h' k k'} → h ⊑ʰ h' → k ⊑ʰ k' → h +ʰ k ⊑ʰ h' +ʰ k'
+ʰ-mono {h' = h'} {k = k} r r' = ⊑ʰ-trans (+ʰ-monoˡ k r) (+ʰ-monoʳ h' r')

-- an upper end at least `0 ∣ ⁺` does not shrink what it is added to

+ʰ-inflate : ∀ h {h'} → fin 0⁺ ⊑ʰ h' → h ⊑ʰ h +ʰ h'
+ʰ-inflate h {h'} r =
  subst (_⊑ʰ h +ʰ h') (+ʰ-identityʳ h) (+ʰ-monoʳ h r)

------------------------------------------------------------------------
-- A lower end strictly below an upper end

infix 4 _◁_ _◁?_

_◁_ : Cut → Hi → Set
c ◁ fin c' = c ⊏ c'
c ◁ ∞      = ⊤

_◁?_ : Decidable _◁_
c ◁? fin c' with c' ⊑? c
... | yes p = no λ q → q p
... | no ¬p = yes ¬p
c ◁? ∞ = yes tt

⊑-◁-trans : ∀ {c c' h} → c ⊑ c' → c' ◁ h → c ◁ h
⊑-◁-trans {h = fin _} p q = ⊑-⊏-trans p q
⊑-◁-trans {h = ∞}     _ _ = tt

◁-⊑ʰ-trans : ∀ {c h h'} → c ◁ h → h ⊑ʰ h' → c ◁ h'
◁-⊑ʰ-trans {h = fin _} {fin _} p q = ⊏-⊑-trans p q
◁-⊑ʰ-trans {h = _}     {∞}     _ _ = tt
◁-⊑ʰ-trans {h = ∞}     {fin _} _ ()

-- an upper end above a lower one is at least `0 ∣ ⁺`

◁⇒0⁺⊑ʰ : ∀ {c h} → c ◁ h → fin 0⁺ ⊑ʰ h
◁⇒0⁺⊑ʰ {c} {fin _} p = 0⁻⊏⇒0⁺⊑ (⊑-⊏-trans (0⁻-least c) p)
◁⇒0⁺⊑ʰ {c} {∞}     _ = tt

-- sums keep a lower end below an upper one

+-◁ : ∀ {c c' h h'} → c ◁ h → c' ◁ h' → c +ˡ c' ◁ h +ʰ h'
+-◁ {p ∣ s} {p' ∣ s'} {fin (q ∣ t)} {fin (q' ∣ t')} r r'
  with ⊏-cases r | ⊏-cases r'
... | inj₁ a | _ =
  ⊏-by-pt (<-≤-trans (+ᴰ-monoˡ-< p' a) (+ᴰ-monoʳ-≤ q (pt≤ r')))
  where
    pt≤ : ∀ {c c'} → c ⊏ c' → pt c ≤ᴰ pt c'
    pt≤ x with ⊏-cases x
    ... | inj₁ b          = <⇒≤ b
    ... | inj₂ (e , _ , _) = ≤ᴰ-reflexive e
... | inj₂ (e , _ , _) | inj₁ a' =
  ⊏-by-pt (≤-<-trans (≤ᴰ-reflexive (cong (_+ᴰ p') e)) (+ᴰ-monoʳ-< q a'))
... | inj₂ (e , refl , refl) | inj₂ (e' , refl , refl) =
  ⊏-by-side (cong₂ _+ᴰ_ e e')
+-◁ {_ ∣ _} {_ ∣ _} {fin (_ ∣ _)} {∞}     _ _ = tt
+-◁ {_ ∣ _} {_ ∣ _} {∞}           {_}     _ _ = tt

------------------------------------------------------------------------
-- Intervals

record Interval : Set where
  constructor ⟪_,_⟫
  field
    lo     : Cut
    hi     : Hi
    {lo◁hi?} : True (lo ◁? hi)

open Interval public

lo◁hi : (i : Interval) → lo i ◁ hi i
lo◁hi i = toWitness {a? = lo i ◁? hi i} (lo◁hi? i)

-- two intervals with the same ends are equal

eqⁱ : ∀ {i j} → lo i ≡ lo j → hi i ≡ hi j → i ≡ j
eqⁱ {_} {j} refl refl = cong (λ x → ⟪ lo j , hi j ⟫ {x}) (T-irrelevant _ _)

-- the order: the ends of the smaller interval lie within those of the
-- larger

infix 4 _⊆ⁱ_ _⊆ⁱ?_

_⊆ⁱ_ : Interval → Interval → Set
i ⊆ⁱ j = lo j ⊑ lo i × hi i ⊑ʰ hi j

_⊆ⁱ?_ : Decidable _⊆ⁱ_
i ⊆ⁱ? j with lo j ⊑? lo i | hi i ⊑ʰ? hi j
... | yes p | yes q = yes (p , q)
... | no ¬p | _     = no λ r → ¬p (proj₁ r)
... | _     | no ¬q = no λ r → ¬q (proj₂ r)

⊆ⁱ-refl : ∀ {i} → i ⊆ⁱ i
⊆ⁱ-refl = ⊑-refl , ⊑ʰ-refl

⊆ⁱ-trans : ∀ {i j k} → i ⊆ⁱ j → j ⊆ⁱ k → i ⊆ⁱ k
⊆ⁱ-trans (p , q) (p' , q') = ⊑-trans p' p , ⊑ʰ-trans q q'

⊆ⁱ-antisym : ∀ {i j} → i ⊆ⁱ j → j ⊆ⁱ i → i ≡ j
⊆ⁱ-antisym (p , q) (p' , q') = eqⁱ (⊑-antisym p' p) (⊑ʰ-antisym q q')

-- the sum, the unit, the top and the hull

infixl 7 _⊕_
infixl 6 _∪ⁱ_

_⊕_ : Interval → Interval → Interval
i ⊕ j = ⟪ lo i +ˡ lo j , hi i +ʰ hi j ⟫
          {fromWitness (+-◁ {lo i} {lo j} {hi i} {hi j} (lo◁hi i) (lo◁hi j))}

-- the interval of exactly `p`

pointⁱ : Carrier → Interval
pointⁱ p = ⟪ p ∣ ⁻ , fin (p ∣ ⁺) ⟫ {fromWitness (⊏-by-side refl)}

0ⁱ : Interval
0ⁱ = pointⁱ 0ᴰ

⊤ⁱ : Interval
⊤ⁱ = ⟪ 0⁻ , ∞ ⟫

_∪ⁱ_ : Interval → Interval → Interval
i ∪ⁱ j = ⟪ lo i ⊓ᶜ lo j , hi i ⊔ʰ hi j ⟫
           {fromWitness (⊑-◁-trans (⊓ᶜ-lbˡ (lo i) (lo j))
                           (◁-⊑ʰ-trans {lo i} {hi i} (lo◁hi i) (⊔ʰ-ubˡ (hi i) (hi j))))}

-- monoid laws

⊕-identityˡ : ∀ i → 0ⁱ ⊕ i ≡ i
⊕-identityˡ i = eqⁱ (+ˡ-identityˡ (lo i)) (+ʰ-identityˡ (hi i))

⊕-identityʳ : ∀ i → i ⊕ 0ⁱ ≡ i
⊕-identityʳ i = eqⁱ (+ˡ-identityʳ (lo i)) (+ʰ-identityʳ (hi i))

⊕-assoc : ∀ i j k → (i ⊕ j) ⊕ k ≡ i ⊕ (j ⊕ k)
⊕-assoc i j k = eqⁱ (+ˡ-assoc (lo i) (lo j) (lo k)) (+ʰ-assoc (hi i) (hi j) (hi k))

⊕-comm : ∀ i j → i ⊕ j ≡ j ⊕ i
⊕-comm i j = eqⁱ (+ˡ-comm (lo i) (lo j)) (+ʰ-comm (hi i) (hi j))

pointⁱ-+ : ∀ p q → pointⁱ (p +ᴰ q) ≡ pointⁱ p ⊕ pointⁱ q
pointⁱ-+ p q = eqⁱ refl refl

-- the order against the operations

⊆ⁱ-⊤ : ∀ i → i ⊆ⁱ ⊤ⁱ
⊆ⁱ-⊤ i = 0⁻-least (lo i) , ⊑ʰ-∞ (hi i)

⊕-mono : ∀ {i i' j j'} → i ⊆ⁱ i' → j ⊆ⁱ j' → i ⊕ j ⊆ⁱ i' ⊕ j'
⊕-mono (p , q) (p' , q') = +ˡ-mono p p' , +ʰ-mono q q'

∪ⁱ-ubˡ : ∀ i j → i ⊆ⁱ i ∪ⁱ j
∪ⁱ-ubˡ i j = ⊓ᶜ-lbˡ (lo i) (lo j) , ⊔ʰ-ubˡ (hi i) (hi j)

∪ⁱ-ubʳ : ∀ i j → j ⊆ⁱ i ∪ⁱ j
∪ⁱ-ubʳ i j = ⊓ᶜ-lbʳ (lo i) (lo j) , ⊔ʰ-ubʳ (hi i) (hi j)

∪ⁱ-lub : ∀ {i j k} → i ⊆ⁱ k → j ⊆ⁱ k → i ∪ⁱ j ⊆ⁱ k
∪ⁱ-lub (p , q) (p' , q') = ⊓ᶜ-glb p p' , ⊔ʰ-lub q q'

-- the sums of ends distribute over the smaller lower end and the
-- larger upper end

+ˡ-distrib-⊓ᶜ : ∀ c d e → (c +ˡ d) ⊓ᶜ (c +ˡ e) ⊑ c +ˡ (d ⊓ᶜ e)
+ˡ-distrib-⊓ᶜ c d e with ⊓ᶜ-sel d e
... | inj₁ eq = subst (λ x → (c +ˡ d) ⊓ᶜ (c +ˡ e) ⊑ c +ˡ x) (sym eq) (⊓ᶜ-lbˡ (c +ˡ d) (c +ˡ e))
... | inj₂ eq = subst (λ x → (c +ˡ d) ⊓ᶜ (c +ˡ e) ⊑ c +ˡ x) (sym eq) (⊓ᶜ-lbʳ (c +ˡ d) (c +ˡ e))

+ʰ-distrib-⊔ʰ : ∀ h k k' → h +ʰ (k ⊔ʰ k') ⊑ʰ (h +ʰ k) ⊔ʰ (h +ʰ k')
+ʰ-distrib-⊔ʰ h k k' with ⊔ʰ-sel k k'
... | inj₁ eq = subst (λ x → h +ʰ x ⊑ʰ (h +ʰ k) ⊔ʰ (h +ʰ k')) (sym eq) (⊔ʰ-ubˡ (h +ʰ k) (h +ʰ k'))
... | inj₂ eq = subst (λ x → h +ʰ x ⊑ʰ (h +ʰ k) ⊔ʰ (h +ʰ k')) (sym eq) (⊔ʰ-ubʳ (h +ʰ k) (h +ʰ k'))

-- the sum distributes over the hull

⊕-distribˡ-∪ⁱ : ∀ i j k → i ⊕ (j ∪ⁱ k) ⊆ⁱ (i ⊕ j) ∪ⁱ (i ⊕ k)
⊕-distribˡ-∪ⁱ i j k = +ˡ-distrib-⊓ᶜ (lo i) (lo j) (lo k) , +ʰ-distrib-⊔ʰ (hi i) (hi j) (hi k)

⊕-distribʳ-∪ⁱ : ∀ i j k → (j ∪ⁱ k) ⊕ i ⊆ⁱ (j ⊕ i) ∪ⁱ (k ⊕ i)
⊕-distribʳ-∪ⁱ i j k =
  subst₂ _⊆ⁱ_ (⊕-comm i (j ∪ⁱ k))
              (cong₂ _∪ⁱ_ (⊕-comm i j) (⊕-comm i k))
         (⊕-distribˡ-∪ⁱ i j k)

-- zero-product: a sum within the unit has its summands within it

⊆ⁱ-0ⁱ-sumˡ : ∀ i j → i ⊕ j ⊆ⁱ 0ⁱ → i ⊆ⁱ 0ⁱ
⊆ⁱ-0ⁱ-sumˡ i j (_ , q) =
  0⁻-least (lo i) ,
  ⊑ʰ-trans (+ʰ-inflate (hi i) (◁⇒0⁺⊑ʰ {lo j} {hi j} (lo◁hi j))) q

⊆ⁱ-0ⁱ-sumʳ : ∀ i j → i ⊕ j ⊆ⁱ 0ⁱ → j ⊆ⁱ 0ⁱ
⊆ⁱ-0ⁱ-sumʳ i j r = ⊆ⁱ-0ⁱ-sumˡ j i (subst (_⊆ⁱ 0ⁱ) (⊕-comm i j) r)

------------------------------------------------------------------------
-- The closure: the same lower end, and an upper end that only the
-- point zero or no bound absorbs

plusʰ : Hi → Hi
plusʰ (fin c) with c ⊑? 0⁺
... | yes _ = fin c
... | no _  = ∞
plusʰ ∞ = ∞

⊑ʰ-plusʰ : ∀ h → h ⊑ʰ plusʰ h
⊑ʰ-plusʰ (fin c) with c ⊑? 0⁺
... | yes _ = ⊑-refl
... | no _  = tt
⊑ʰ-plusʰ ∞ = tt

-- an upper end that is at least `0 ∣ ⁺` and at most it is it

0⁺-pinned : ∀ {c} → 0⁺ ⊑ c → c ⊑ 0⁺ → c ≡ 0⁺
0⁺-pinned p q = ⊑-antisym q p

-- an upper end above `0 ∣ ⁺` strictly grows what it is added to

+ʰ-grows : ∀ {c} → ¬ (c ⊑ 0⁺) → ∀ c' → ¬ (fin c +ʰ fin c' ⊑ʰ fin c')
+ʰ-grows {p ∣ s} ¬r (q ∣ t) r with compare 0ᴰ p
... | tri< a    = ⊏-by-pt (<-+ˡ a) r
... | tri≈ refl = ¬r (by-side refl ≤ˢ-⁺)
... | tri> a    = a (0ᴰ-least p)

-- a cut summing with itself to at most itself lies at zero

+-self : ∀ {c} → fin c +ʰ fin c ⊑ʰ fin c → c ⊑ 0⁺
+-self {p ∣ s} (by-pt a) = ⊥-elim-irr (a (≤ᴰ-+ p p))
+-self {p ∣ s} (by-side e _) rewrite +ᴰ-absorbʳ e = by-side refl ≤ˢ-⁺

plusʰ-iter : ∀ {h} → fin 0⁺ ⊑ʰ h → plusʰ h +ʰ plusʰ h ⊑ʰ plusʰ h
plusʰ-iter {fin c} r with c ⊑? 0⁺
... | yes q rewrite ⊑-antisym q r = by-side (+ᴰ-identityˡ 0ᴰ) ⁺≤⁺
... | no _  = tt
plusʰ-iter {∞} _ = tt

plusʰ-least : ∀ {h v} → h ⊑ʰ v → v +ʰ v ⊑ʰ v → plusʰ h ⊑ʰ v
plusʰ-least {fin c} {v} r r' with c ⊑? 0⁺
... | yes _ = r
plusʰ-least {fin c} {fin d} r r' | no ¬q = ¬q (⊑-trans r (+-self r'))
plusʰ-least {fin c} {∞}     r r' | no ¬q = tt
plusʰ-least {∞}     {∞}     _ _ = tt
plusʰ-least {∞}     {fin _} () _

plusʰ-indˡ : ∀ {h k} → h +ʰ k ⊑ʰ k → plusʰ h +ʰ k ⊑ʰ k
plusʰ-indˡ {fin c} {k} r with c ⊑? 0⁺
... | yes _ = r
plusʰ-indˡ {fin c} {fin d} r | no ¬q = ⊥-elim (+ʰ-grows ¬q d r)
plusʰ-indˡ {fin c} {∞}     r | no ¬q = tt
plusʰ-indˡ {∞}     {k}     r = r

plusʰ-indʳ : ∀ {h k} → k +ʰ h ⊑ʰ k → k +ʰ plusʰ h ⊑ʰ k
plusʰ-indʳ {h} {k} r =
  subst (_⊑ʰ k) (+ʰ-comm (plusʰ h) k)
        (plusʰ-indˡ {h} {k} (subst (_⊑ʰ k) (+ʰ-comm k h) r))

i⁺ : Interval → Interval
i⁺ i = ⟪ lo i , plusʰ (hi i) ⟫
         {fromWitness (◁-⊑ʰ-trans {lo i} {hi i} (lo◁hi i) (⊑ʰ-plusʰ (hi i)))}

⊆ⁱ-irrelevant : ∀ {i j} (p q : i ⊆ⁱ j) → p ≡ q
⊆ⁱ-irrelevant {i} {j} (p , q) (p' , q') =
  cong₂ _,_ (⊑-irrelevant p p') (⊑ʰ-irrelevant {hi i} {hi j} q q')
