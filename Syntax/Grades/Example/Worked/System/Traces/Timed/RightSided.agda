------------------------------------------------------------------------
-- Worked instance: forgetting the runs, keeping the deadline.         --
--
-- `System.Traces.Timed.RightSided` measures a grade of trace bounds by  --
-- its slowest bound. The effect grade still says which runs are         --
-- permitted and which operations they may perform; the resource grade   --
-- keeps only how long they may take.                                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Traces.Timed.RightSided where

open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using (↑_; ∞)

open import Syntax.Grades.Example.Time.RightSided
  using () renaming (𝕀ᵣ to 𝕀ʳ; [0,_] to mkᵣ; _≾ₒ_ to _≾ᵣ_; _·ₒ_ to _·ᵣ_)

-- and every deadline a finite one

[0,_] : ℕ → 𝕀ʳ
[0, n ] = mkᵣ (↑ n)

open import Syntax.Grades.Example.System.Traces.Timed.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (traces→right-sided-intervals)

open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
  using (_≾_; holds; within_; unbounded; _·ᵇ_)
  renaming (⟅_⟆ to ⟅_⟆ʰⁱ; ⟅_∣_⟆ to ⟅_∣_⟆ʰⁱ)

-- a reading and six ticks' worth of work is a seven-tick deadline

budget-measured :
  map traces→right-sided-intervals (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ) ≡ [0, 7 ]
budget-measured = refl

-- and a grade listing alternatives is measured by the slowest of them

alternatives-measured :
  map traces→right-sided-intervals
      (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ʰⁱ)
  ≡ [0, 12 ]
alternatives-measured = refl

-- the unbounded grade becomes the deadline that is no deadline

unbounded-measured : map traces→right-sided-intervals unbounded ≡ mkᵣ ∞
unbounded-measured = refl

-- what the projection forgets is which operations are permitted: a
-- bound naming a store and one budgeting the three ticks a store takes
-- become the same deadline, though only the first permits the store
-- outright

operations-forgotten :
  map traces→right-sided-intervals (within ⟅ ⌈ write ⌉ ⟆ʰⁱ)
  ≡ map traces→right-sided-intervals (within ⟅ ⟨ 3 ⟩ ⟆ʰⁱ)
operations-forgotten = refl

-- upstream those two are ordered one way and not the other, which the
-- deadline cannot see

store-within-three-ticks : within ⟅ ⌈ write ⌉ ⟆ʰⁱ ≾ within ⟅ ⟨ 3 ⟩ ⟆ʰⁱ
store-within-three-ticks = holds

-- monotonicity: weakening a grade to a budget raises the deadline with
-- it, from four ticks to seven

deadline-rises :
  map traces→right-sided-intervals (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ʰⁱ)
  ≾ᵣ map traces→right-sided-intervals (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ)
deadline-rises =
  map-monotone traces→right-sided-intervals
               {within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ʰⁱ}
               {within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ} holds

-- and it is a monoid map: sequencing before or after measuring agrees

deadlines-add :
  map traces→right-sided-intervals
      (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ·ᵇ within ⟅ ⌈ send ⌉ ⟆ʰⁱ)
  ≡ map traces→right-sided-intervals (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ)
    ·ᵣ map traces→right-sided-intervals (within ⟅ ⌈ send ⌉ ⟆ʰⁱ)
deadlines-add = refl
