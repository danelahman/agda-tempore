-------------------------------------------------------------------------
-- Reachability in the frame of tick counts.                           --
--                                                                     --
-- In the frame of tick counts with lower time bounds, some world is   --
-- reachable from every world at every grade. This is the hypothesis   --
-- of `reachable⇒tick` in `PSh.HeadFaithful`, which gives a            --
-- `TickFrame`.                                                        --
-------------------------------------------------------------------------

module MonomorphicCalculus.Adequacy.PSh.TickFrames where

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product

open import Grades.Examples.Time.LowerBound using (𝕀; [_,+∞⟩)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.LowerBound
  using (_⊑ᵗ[_]_)

-- "at least `n` ticks" reaches exactly `n` ticks ahead

lower-reachable : ∀ (ρ : 𝕀) (w : ℕ) → Σ[ w' ∈ ℕ ] (w ⊑ᵗ[ ρ ] w')
lower-reachable [ n ,+∞⟩ w = n + w , ≤-refl
