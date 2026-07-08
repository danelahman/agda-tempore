------------------------------------------------------------------------
-- A time-ticks Kripke frame for the left-sided time intervals as the   --
-- resource grades.                                                     --
--                                                                    --
-- Worlds are time points `ℕ`. A left-sided resource grade `[ n ,+∞⟩`   --
-- ("at least `n` ticks") reaches every world at least `n` ticks ahead:  --
--                                                                    --
--   w ⊑ʳ[ [ n ,+∞⟩ ] w'   iff   n + w ≤ w'                             --
--                                                                    --
-- Multiplying grades (`·ₒ`) adds the lower bounds, so composing two     --
-- accessibilities advances the world by the sum of their ticks.         --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.LeftSidedIntervalsWithTicks where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant;
         +-monoˡ-≤; +-monoʳ-≤; +-comm; +-assoc)

open import Syntax.Grades.LeftSidedTimeIntervals
  using (𝕀; [_,+∞⟩; _·ₒ_; _≾ₒ_; left-sided-intervals)

open import Util.Equality

open import DenotationalSemantics.Model.World

-- Accessibility on time ticks: reach any world at least `n` ticks ahead.

_⊑ᵗ[_]_ : ℕ → 𝕀 → ℕ → Set
w ⊑ᵗ[ [ n ,+∞⟩ ] w' = n + w ≤ w'

-- reflexivity at the unit grade `[ 0 ,+∞⟩`

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ [ 0 ,+∞⟩ ] w
⊑ᵗ-refl = ≤-refl

-- transitivity multiplies the grades (adds the lower bounds)

⊑ᵗ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ᵗ[ ρ₁ ] w' → w' ⊑ᵗ[ ρ₂ ] w'' → w ⊑ᵗ[ ρ₁ ·ₒ ρ₂ ] w''
⊑ᵗ-trans {[ m ,+∞⟩} {[ n ,+∞⟩} {w} p q =
  ≤-trans (≤-reflexive (trans (cong (_+ w) (+-comm m n)) (+-assoc n m w)))
          (≤-trans (+-monoʳ-≤ n p) q)

-- covariance: a smaller lower bound (a larger interval) gives a larger
-- relation

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ₒ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {[ m ,+∞⟩} {[ n ,+∞⟩} {w} rel p = ≤-trans (+-monoˡ-≤ w rel) p

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant {[ _ ,+∞⟩} p q = ≤-irrelevant p q

-- The frame.

ticks : World left-sided-intervals
ticks = record
  { W             = ℕ
  ; _⊑ʳ[_]_       = _⊑ᵗ[_]_
  ; ⊑ʳ-refl       = ⊑ᵗ-refl
  ; ⊑ʳ-trans      = ⊑ᵗ-trans
  ; ⊑ʳ-mono       = ⊑ᵗ-mono
  ; ⊑ʳ-irrelevant = ⊑ᵗ-irrelevant
  }
