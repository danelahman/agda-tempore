------------------------------------------------------------------------
-- The concrete tick frames can always let time pass.                  --
--                                                                     --
-- Checks `PSh.HeadFaithful`'s `TickFrame` premise — some world is     --
-- reachable at every grade — holds for the simplest concrete frame.   --
------------------------------------------------------------------------

module OperationalSemantics.Adequacy.PSh.TickFrames where

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩)

open import DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSided
  using (_⊑ᵗ[_]_)

-- "at least `n` ticks" reaches exactly `n` ticks ahead

lsi-reachable : ∀ (ρ : 𝕀) (w : ℕ) → Σ[ w' ∈ ℕ ] (w ⊑ᵗ[ ρ ] w')
lsi-reachable [ n ,+∞⟩ w = n + w , ≤-refl
