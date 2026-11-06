------------------------------------------------------------------------
-- Worked instance: forgetting the runs, keeping the deadline.        --
--                                                                    --
-- `System.Traces.Banked.UpperBound` measures a grade of trace bounds --
-- by its slowest bound. The effect grade records which runs are      --
-- permitted and which operations they may perform; the resource      --
-- grade records only how long they may take.                         --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.Banked.UpperBound where

open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Grades.Examples.Time.Interval using (↑_; ∞)

open import Grades.Examples.Time.UpperBound
  using () renaming (𝕀ᵣ to 𝕀ʳ; [0,_] to mkᵣ; _≾ₒ_ to _≾ᵣ_; _·ₒ_ to _·ᵣ_)

-- and every deadline a finite one

[0,_] : ℕ → 𝕀ʳ
[0, n ] = mkᵣ (↑ n)

open import Grades.Examples.System.Traces.Banked.UpperBound
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (banked→upper-bounds)

open import Grades.Examples.Worked.Traces.Banked.UpperBound
  using (_≾_; holds; within_; unbounded; _·ᵇ_)
  renaming (⟅_⟆ to ⟅_⟆ʰⁱ; ⟅_∣_⟆ to ⟅_∣_⟆ʰⁱ)

-- a reading and six ticks' worth of work is a seven-tick deadline

budget-measured :
  map banked→upper-bounds (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ) ≡ [0, 7 ]
budget-measured = refl

-- and a grade listing alternatives is measured by the slowest of them

alternatives-measured :
  map banked→upper-bounds
      (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ʰⁱ)
  ≡ [0, 12 ]
alternatives-measured = refl

-- the unbounded grade becomes the deadline that is no deadline

unbounded-measured : map banked→upper-bounds unbounded ≡ mkᵣ ∞
unbounded-measured = refl

-- what the projection forgets is which operations are permitted: a
-- bound naming a store and one budgeting the three ticks a store takes
-- become the same deadline, though only the first permits the store
-- outright

operations-forgotten :
  map banked→upper-bounds (within ⟅ ⌈ write ⌉ ⟆ʰⁱ)
  ≡ map banked→upper-bounds (within ⟅ ⟨ 3 ⟩ ⟆ʰⁱ)
operations-forgotten = refl

-- upstream those two are ordered one way and not the other, which the
-- deadline cannot see

store-within-three-ticks : within ⟅ ⌈ write ⌉ ⟆ʰⁱ ≾ within ⟅ ⟨ 3 ⟩ ⟆ʰⁱ
store-within-three-ticks = holds

-- monotonicity: weakening a grade to a budget raises the deadline with
-- it, from four ticks to seven

deadline-rises :
  map banked→upper-bounds (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ʰⁱ)
  ≾ᵣ map banked→upper-bounds (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ)
deadline-rises =
  map-monotone banked→upper-bounds
               {within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ʰⁱ}
               {within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ} holds

-- and it is a monoid map: sequencing before or after measuring agrees

deadlines-add :
  map banked→upper-bounds
      (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ·ᵇ within ⟅ ⌈ send ⌉ ⟆ʰⁱ)
  ≡ map banked→upper-bounds (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ)
    ·ᵣ map banked→upper-bounds (within ⟅ ⌈ send ⌉ ⟆ʰⁱ)
deadlines-add = refl
