------------------------------------------------------------------------
-- A time-ticks Kripke frame for the right-sided time intervals as the  --
-- resource grades.                                                     --
--                                                                    --
-- Worlds are time points `ℕ`. A right-sided resource grade `[0, n ]`   --
-- ("at most `n` ticks") reaches the worlds no more than `n` ticks       --
-- ahead:                                                              --
--                                                                    --
--   w ⊑[ [0, n ] ] w'   iff   w' ≤ w + n                              --
--                                                                    --
-- the mirror image of `Time.LeftSided`'s frame, which asks the world    --
-- to advance by *at least* the bound. Multiplying grades adds the       --
-- bounds, so composing two accessibilities advances by at most their    --
-- sum, and a larger bound -- the weaker grade -- gives a larger         --
-- relation.                                                           --
--                                                                    --
-- Together with `Time.LeftSided` and `Time.TwoSided` this completes the --
-- interval family: every grade `Grades.Example.Time` defines has a      --
-- tick frame, and the frame's direction is read off the grade's.        --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant;
         +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-identityʳ)

open import Syntax.Grades.Example.Time.RightSided
  using (𝕀ᵣ; [0,_]; _·ₒ_; _≾ₒ_; right-sided-intervals)

open import Util.Equality

open import DenotationalSemantics.Model.World

-- Accessibility on time ticks: reach the worlds at most `n` ticks ahead.

_⊑ᵗ[_]_ : ℕ → 𝕀ᵣ → ℕ → Set
w ⊑ᵗ[ [0, n ] ] w' = w' ≤ w + n

-- reflexivity at the unit grade `[0, 0 ]`: the world does not move

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ [0, 0 ] ] w
⊑ᵗ-refl {w} = ≤-reflexive (sym (+-identityʳ w))

-- transitivity multiplies the grades (adds the upper bounds): the two
-- advances compose into one of at most the sum

⊑ᵗ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ᵗ[ ρ₁ ] w' → w' ⊑ᵗ[ ρ₂ ] w'' → w ⊑ᵗ[ ρ₁ ·ₒ ρ₂ ] w''
⊑ᵗ-trans {[0, m ]} {[0, n ]} {w} p q =
  ≤-trans (≤-trans q (+-monoˡ-≤ n p)) (≤-reflexive (+-assoc w m n))

-- covariance: a larger upper bound (a weaker grade) gives a larger
-- relation

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ₒ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {[0, m ]} {[0, n ]} {w} rel p = ≤-trans p (+-monoʳ-≤ w rel)

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant {[0, _ ]} p q = ≤-irrelevant p q

-- The frame.

ticks : World right-sided-intervals
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = ⊑ᵗ-trans
  ; ⊑-mono       = ⊑ᵗ-mono
  ; ⊑-irrelevant = ⊑ᵗ-irrelevant
  }
