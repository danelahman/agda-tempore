------------------------------------------------------------------------
-- Worked instance: the finite run set cap, beside the banked floor.  --
--                                                                    --
-- At the subset order the grade lists the runs, and the deadline is  --
-- the worst case of the slowest of them. The banked floor, on the    --
-- same two runs, takes the fastest; the direction is determined by   --
-- the side the endpoint bounds.                                      --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.FiniteRunSets.UpperBound where

open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Grades.Examples.Time.UpperBound
  using () renaming (𝕀ᵣ to 𝕀ʳ; [0,_] to mkᵣ; _≾ₒ_ to _≾ᵣ_)

open import Grades.Examples.Time.Interval using (↑_)

open import Grades.Examples.System.Traces.FiniteRunSets.UpperBound
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ using (finite-run-sets→upper-bounds)

open import Grades.Examples.System.Traces.Banked.LowerBound
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ using (banked→lower-bounds)

open import Grades.Examples.Time.LowerBound using ([_,+∞⟩)

open import Grades.Examples.Worked.Traces.FiniteRunSets.UpperBound
  using (permitting_) renaming (holds to holdsˢʰ)
open import Grades.Examples.Worked.Traces.Banked.LowerBound
  using () renaming (Antichain to Antichainˡᵒ; ⟅_∣_⟆ to ⟅_∣_⟆ˡᵒ)

-- and every deadline a finite one

[0,_] : ℕ → 𝕀ʳ
[0, n ] = mkᵣ (↑ n)

-- the two branches take one tick and two-to-three ticks

the-branches : NeTraces
the-branches = ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆

the-branchesˡᵒ : Antichainˡᵒ
the-branchesˡᵒ = ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ˡᵒ

-- the deadline is the slower branch at its worst case

cap-measured :
  map finite-run-sets→upper-bounds (permitting the-branches) ≡ [0, 3 ]
cap-measured = refl

-- where the banked floor, guaranteeing one of its alternatives rather
-- than a particular one, promises only what the faster of them takes

banked-floor-measured :
  map banked→lower-bounds the-branchesˡᵒ ≡ [ 1 ,+∞⟩
banked-floor-measured = refl

-- monotonicity: permitting a further run raises the deadline

cap-deadline-rises :
  map finite-run-sets→upper-bounds (permitting ⟅ ⌈ read ⌉ ⟆)
  ≾ᵣ map finite-run-sets→upper-bounds (permitting the-branches)
cap-deadline-rises =
  map-monotone finite-run-sets→upper-bounds
               {permitting ⟅ ⌈ read ⌉ ⟆} {permitting the-branches} holdsˢʰ
