------------------------------------------------------------------------
-- A time-ticks Kripke frame for the right-sided time intervals as the --
-- resource grades.                                                    --
--                                                                     --
-- Worlds are time points `ℕ`. A right-sided resource grade `[0, n ]`  --
-- ("at most `n` ticks", with `n : ℕ∞`) reaches the worlds ahead by at --
-- most `n` ticks, an infinite `n` bounding nothing:                   --
--                                                                     --
--   w ⊑[ [0, n ] ] w'   iff   w ≤ w'   and   ↑ w' ≤∞ ↑ w +∞ n         --
--                                                                     --
-- the mirror image of `Time.LeftSided`'s frame, which asks the world  --
-- to advance by *at least* the bound. Multiplying grades adds the     --
-- bounds, so composing two accessibilities advances by at most their  --
-- sum, and a larger bound -- the weaker grade -- gives a larger       --
-- relation.                                                           --
--                                                                     --
-- It is the upper bound restricted to forward moves: the unit is      --
-- least, so without `w ≤ w'` the unit grade would reach the past.     --
--                                                                     --
-- Together with `Time.LeftSided` and `Time.TwoSidedWithInfinity` this --
-- completes the interval family: every grade `Grades.Example.Time`    --
-- defines has a tick frame, and the frame's direction is read off the --
-- grade's.                                                            --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant; +-identityʳ)
open import Data.Product using (_×_)

open import Syntax.Grades.Example.Time.RightSided
  using (𝕀ᵣ; [0,_]; _·ₒ_; _≾ₒ_; right-sided-intervals;
         ℕ∞; ↑_; ∞; _+∞_; _≤∞_; +∞-mono-≤∞; ≤∞-refl; ≤∞-trans; ≤∞-irrelevant;
         +∞-assoc)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Action using (forward)

-- ℕ∞ helper used to rearrange the bound

≤∞-reflexive : ∀ {a b} → a ≡ b → a ≤∞ b
≤∞-reflexive refl = ≤∞-refl

-- The upper bound: reach no further than `n` ticks ahead.

_⊑ᵗ[_]_ : ℕ → 𝕀ᵣ → ℕ → Set
w ⊑ᵗ[ [0, n ] ] w' = ↑ w' ≤∞ (↑ w +∞ n)

-- reflexivity at the unit grade `[0, ↑ 0 ]`

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ [0, ↑ 0 ] ] w
⊑ᵗ-refl {w} = ≤-reflexive (sym (+-identityʳ w))

-- transitivity multiplies the grades (adds the upper bounds): the two
-- advances compose into one of at most the sum

⊑ᵗ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ᵗ[ ρ₁ ] w' → w' ⊑ᵗ[ ρ₂ ] w'' → w ⊑ᵗ[ ρ₁ ·ₒ ρ₂ ] w''
⊑ᵗ-trans {[0, m ]} {[0, n ]} {w} {w'} p q =
  ≤∞-trans q
    (≤∞-trans (+∞-mono-≤∞ {↑ w'} {n} {↑ w +∞ m} {n} p (≤∞-refl {n}))
              (≤∞-reflexive (+∞-assoc (↑ w) m n)))

-- covariance: a larger upper bound (a weaker grade) gives a larger
-- relation

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ₒ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {[0, m ]} {[0, n ]} {w} {w'} rel p =
  ≤∞-trans p (+∞-mono-≤∞ {↑ w} {m} {↑ w} {n} (≤∞-refl {↑ w}) rel)

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant {[0, n ]} {w} {w'} = ≤∞-irrelevant {↑ w'} {↑ w +∞ n}

-- the bound as a frame

private
  bounded : World right-sided-intervals
  bounded = record
    { W             = ℕ
    ; _⊑[_]_       = _⊑ᵗ[_]_
    ; ⊑-refl       = ⊑ᵗ-refl
    ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
    ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
    ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
    }

-- The frame: the bound, forward moves only.

ticks : World right-sided-intervals
ticks = forward bounded _≤_ ≤-refl ≤-trans ≤-irrelevant

-- the relation it states

⊑-def : ∀ {w n w'}
      → World._⊑[_]_ ticks w [0, n ] w' ≡ ((w ≤ w') × (↑ w' ≤∞ (↑ w +∞ n)))
⊑-def = refl
