------------------------------------------------------------------------
-- Worked instance: forgetting the runs, keeping the guarantee.       --
--                                                                    --
-- `System.Traces.Banked.LowerBound` measures a grade of guarantees   --
-- by its fastest member. The set is read disjunctively, and the time --
-- guaranteed is that of the cheapest member.                         --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.Banked.LowerBound where

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Grades.Examples.Time.LowerBound using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

open import Grades.Examples.System.Traces.Banked.LowerBound
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ using (traces→lower-bounds)

open import Grades.Examples.Worked.Traces.Banked.LowerBound
  using () renaming (holds to holdsᶜ; Antichain to Antichainˡᵒ; _·_ to _·ˡᵒ_;
                     ⟅_⟆ to ⟅_⟆ˡᵒ; ⟅_∣_⟆ to ⟅_∣_⟆ˡᵒ)

-- a reading, two ticks' settling and a transmission guarantee seven
-- ticks, the two operations credited at their best case

guarantee-measured :
  map traces→lower-bounds ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ˡᵒ ≡ [ 7 ,+∞⟩
guarantee-measured = refl

-- and a grade listing alternatives is measured by the fastest of them,
-- which is the reverse of what the cap's projection does

alternatives-measured-below :
  map traces→lower-bounds
      ⟅ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆ˡᵒ
  ≡ [ 1 ,+∞⟩
alternatives-measured-below = refl

-- what the projection forgets is again which operations occurred: a
-- guarantee that a store happened and one that two ticks passed
-- become the same lower bound, though only the first guarantees the
-- store

stores-forgotten :
  map traces→lower-bounds ⟅ ⌈ write ⌉ ⟆ˡᵒ
  ≡ map traces→lower-bounds ⟅ ⟨ 2 ⟩ ⟆ˡᵒ
stores-forgotten = refl

-- monotonicity: dropping to the reading alone drops the guarantee from
-- seven ticks to one

guarantee-falls :
  map traces→lower-bounds ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ˡᵒ
  ≾ₒ map traces→lower-bounds ⟅ ⌈ read ⌉ ⟆ˡᵒ
guarantee-falls =
  map-monotone traces→lower-bounds
               {⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ˡᵒ} {⟅ ⌈ read ⌉ ⟆ˡᵒ} holdsᶜ

-- and it is a monoid map: sequencing before or after measuring agrees

guarantees-add :
  map traces→lower-bounds (⟅ ⌈ read ⌉ ⟆ˡᵒ ·ˡᵒ ⟅ ⌈ send ⌉ ⟆ˡᵒ)
  ≡ map traces→lower-bounds ⟅ ⌈ read ⌉ ⟆ˡᵒ
    ·ₒ map traces→lower-bounds ⟅ ⌈ send ⌉ ⟆ˡᵒ
guarantees-add = refl
