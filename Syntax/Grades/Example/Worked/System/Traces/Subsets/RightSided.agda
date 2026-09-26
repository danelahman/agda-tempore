------------------------------------------------------------------------
-- Worked instance: the subset cap, beside the timed floor.           --
--                                                                    --
-- At the subset order the grade lists the runs, and the deadline is  --
-- the worst case of the slowest of them. The timed floor, on the     --
-- same two runs, takes the fastest; the direction is determined by   --
-- the side the endpoint bounds.                                      --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Traces.Subsets.RightSided where

open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Syntax.Grades.Example.Time.RightSided
  using () renaming (𝕀ᵣ to 𝕀ʳ; [0,_] to mkᵣ; _≾ₒ_ to _≾ᵣ_)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using (↑_)

open import Syntax.Grades.Example.System.Traces.Subsets.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ using (subsets→right-sided-intervals)

open import Syntax.Grades.Example.System.Traces.Timed.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ using (traces→left-sided-intervals)

open import Syntax.Grades.Example.Time.LeftSided using ([_,+∞⟩)

open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
  using (permitting_) renaming (holds to holdsˢʰ)
open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
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
  map subsets→right-sided-intervals (permitting the-branches) ≡ [0, 3 ]
cap-measured = refl

-- where the timed floor, guaranteeing one of its alternatives rather
-- than a particular one, promises only what the faster of them takes

timed-floor-measured :
  map traces→left-sided-intervals the-branchesˡᵒ ≡ [ 1 ,+∞⟩
timed-floor-measured = refl

-- monotonicity: permitting a further run raises the deadline

cap-deadline-rises :
  map subsets→right-sided-intervals (permitting ⟅ ⌈ read ⌉ ⟆)
  ≾ᵣ map subsets→right-sided-intervals (permitting the-branches)
cap-deadline-rises =
  map-monotone subsets→right-sided-intervals
               {permitting ⟅ ⌈ read ⌉ ⟆} {permitting the-branches} holdsˢʰ
