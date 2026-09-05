------------------------------------------------------------------------
-- The concrete tick frames can always let time pass.                  --
--                                                                    --
-- `PSh.HeadFaithful`'s `TickFrame` is what the head observation needs --
-- of the frame: a world to observe at, and a one-tick step out of     --
-- every world. This module checks it is not vacuous, at the premise   --
-- `reachable⇒tick` asks for — *some* world is reachable at every      --
-- grade — for the simplest concrete frame.                            --
--                                                                    --
-- Every frame in `Model.Example.World.Ticks` has `W = ℕ` and is       --
-- reachable in the same way: the two-sided intervals land at          --
-- `min i + w` (inside `max i + w` since `min i ≤ max i`), and the     --
-- trace frames at `w + duration t` for any trace `t` of the grade,    --
-- which is nonempty by construction.                                  --
------------------------------------------------------------------------

module OperationalSemantics.Adequacy.PSh.TickFrames where

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product

open import Syntax.Grades.Example.Interval.LeftSided using (𝕀; [_,+∞⟩)

open import DenotationalSemantics.Model.Example.World.Ticks.LeftSidedIntervals
  using (_⊑ᵗ[_]_)

-- "at least `n` ticks" reaches exactly `n` ticks ahead

lsi-reachable : ∀ (ρ : 𝕀) (w : ℕ) → Σ[ w' ∈ ℕ ] (w ⊑ᵗ[ ρ ] w')
lsi-reachable [ n ,+∞⟩ w = n + w , ≤-refl
