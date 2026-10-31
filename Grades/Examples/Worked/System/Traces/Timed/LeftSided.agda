------------------------------------------------------------------------
-- Worked instance: forgetting the runs, keeping the guarantee.       --
--                                                                    --
-- `System.Traces.Timed.LeftSided` measures a grade of guarantees by  --
-- its fastest member. The set is read disjunctively, and the time    --
-- guaranteed is that of the cheapest member.                         --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.Timed.LeftSided where

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Grades.Examples.Time.LeftSided using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

open import Grades.Examples.System.Traces.Timed.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ using (traces→left-sided-intervals)

open import Grades.Examples.Worked.Traces.Timed.LeftSided
  using () renaming (holds to holdsᶜ; Antichain to Antichainˡᵒ; _·_ to _·ˡᵒ_;
                     ⟅_⟆ to ⟅_⟆ˡᵒ; ⟅_∣_⟆ to ⟅_∣_⟆ˡᵒ)

-- a reading, two ticks' settling and a transmission guarantee seven
-- ticks, the two operations credited at their best case

guarantee-measured :
  map traces→left-sided-intervals ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ˡᵒ ≡ [ 7 ,+∞⟩
guarantee-measured = refl

-- and a grade listing alternatives is measured by the fastest of them,
-- which is the reverse of what the cap's projection does

alternatives-measured-below :
  map traces→left-sided-intervals
      ⟅ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆ˡᵒ
  ≡ [ 1 ,+∞⟩
alternatives-measured-below = refl

-- what the projection forgets is again which operations occurred: a
-- guarantee that a store happened and one that two ticks passed
-- become the same lower bound, though only the first guarantees the
-- store

stores-forgotten :
  map traces→left-sided-intervals ⟅ ⌈ write ⌉ ⟆ˡᵒ
  ≡ map traces→left-sided-intervals ⟅ ⟨ 2 ⟩ ⟆ˡᵒ
stores-forgotten = refl

-- monotonicity: dropping to the reading alone drops the guarantee from
-- seven ticks to one

guarantee-falls :
  map traces→left-sided-intervals ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ˡᵒ
  ≾ₒ map traces→left-sided-intervals ⟅ ⌈ read ⌉ ⟆ˡᵒ
guarantee-falls =
  map-monotone traces→left-sided-intervals
               {⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ˡᵒ} {⟅ ⌈ read ⌉ ⟆ˡᵒ} holdsᶜ

-- and it is a monoid map: sequencing before or after measuring agrees

guarantees-add :
  map traces→left-sided-intervals (⟅ ⌈ read ⌉ ⟆ˡᵒ ·ˡᵒ ⟅ ⌈ send ⌉ ⟆ˡᵒ)
  ≡ map traces→left-sided-intervals ⟅ ⌈ read ⌉ ⟆ˡᵒ
    ·ₒ map traces→left-sided-intervals ⟅ ⌈ send ⌉ ⟆ˡᵒ
guarantees-add = refl
