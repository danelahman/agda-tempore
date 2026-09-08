------------------------------------------------------------------------
-- Worked instances of the grade systems.                              --
--                                                                     --
-- A grade system pairs effect grades -- what a computation may do --   --
-- with resource grades -- what is thereby guaranteed about time -- and --
-- a monoid map `∣_∣ᵉ` projecting the first onto the second. Reading    --
-- the projection tells you what the resource grade may forget.         --
--                                                                     --
-- Each section computes the projection on the sensor node's own grades --
-- and then exercises its monotonicity: an ordering between two effect  --
-- grades must still hold between their images.                        --
--                                                                     --
-- The systems that went with the earlier trace grid are parked under   --
-- `backup/` while the trace grades are rebuilt.                        --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Systems where

open import Data.Product using (_,_)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

------------------------------------------------------------------------
-- Forgetting the upper bound
--
-- `IntervalsToLeftSidedIntervals` keeps the lower endpoint alone. The
-- effect grade says the uplink takes between 7 and 9 ticks; the
-- resource grade says only that at least 7 have passed -- which is what
-- a box modality needs, since it is about data having become available,
-- not about a deadline.

open import Syntax.Grades.Example.Time.TwoSided
  using ([_,_,_]; eqᵢ; _·ᵢ_; _≾ᵢ_)

open import Syntax.Grades.Example.Time.LeftSided
  using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

open import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals
  using (tsi→lsi)

open import Syntax.Grades.Example.Worked.Time
  using (≤!; uplink-window)

-- the projection reads off the lower endpoint

forget-max : map tsi→lsi uplink-window ≡ [ 7 ,+∞⟩
forget-max = refl

-- so two effect grades differing only in their deadline become the same
-- resource grade: that difference is exactly what is forgotten

deadline-forgotten :
  map tsi→lsi [ 7 , 9 , ≤! ] ≡ map tsi→lsi [ 7 , 12 , ≤! ]
deadline-forgotten = refl

-- monotonicity: widening the window to `[ 5 , 12 ]` weakens the lower
-- bound to `[ 5 ,+∞⟩`

forget-max-mono : [ 7 ,+∞⟩ ≾ₒ [ 5 ,+∞⟩
forget-max-mono =
  map-monotone tsi→lsi {uplink-window} {[ 5 , 12 , ≤! ]} (≤! , ≤!)

-- and it is a monoid map: sequencing before or after projecting agrees

forget-max-· : map tsi→lsi ([ 1 , 1 , ≤! ] ·ᵢ [ 6 , 8 , ≤! ])
             ≡ map tsi→lsi [ 1 , 1 , ≤! ] ·ₒ map tsi→lsi [ 6 , 8 , ≤! ]
forget-max-· = refl

------------------------------------------------------------------------
-- Forgetting the runs, keeping the deadline
--
-- `TracesToRightSidedIntervals` measures a grade of trace bounds by its
-- slowest bound. The effect grade still says which runs are permitted
-- and which operations they may perform; the resource grade keeps only
-- how long they may take.

open import Syntax.Grades.Example.Time.RightSided
  using ([0,_]) renaming (_≾ₒ_ to _≾ᵣ_; _·ₒ_ to _·ᵣ_)

open import Syntax.Grades.Example.System.TracesToRightSidedIntervals
  Op _≟ₒ_ cost cost-pos using (traces→right-sided-intervals)

open import Syntax.Grades.Example.Worked.Traces.Allowance
  using (_≾_; holds)

-- a reading and six ticks' worth of work is a seven-tick deadline

budget-measured : map traces→right-sided-intervals ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ≡ [0, 7 ]
budget-measured = refl

-- and a grade listing alternatives is measured by the slowest of them

alternatives-measured :
  map traces→right-sided-intervals
      ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≡ [0, 12 ]
alternatives-measured = refl

-- what the projection forgets is which operations are permitted: a
-- bound naming a store and one budgeting the three ticks a store takes
-- become the same deadline, though only the first permits the store
-- outright

operations-forgotten :
  map traces→right-sided-intervals ⟅ ⌈ write ⌉ ⟆
  ≡ map traces→right-sided-intervals ⟅ ⟨ 3 ⟩ ⟆
operations-forgotten = refl

-- upstream those two are ordered one way and not the other, which the
-- deadline cannot see

store-within-three-ticks : ⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 3 ⟩ ⟆
store-within-three-ticks = holds

-- monotonicity: weakening a grade to a budget raises the deadline with
-- it, from four ticks to seven

deadline-rises :
  map traces→right-sided-intervals ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ᵣ map traces→right-sided-intervals ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
deadline-rises =
  map-monotone traces→right-sided-intervals
               {⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆} {⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆} holds

-- and it is a monoid map: sequencing before or after measuring agrees

deadlines-add :
  map traces→right-sided-intervals (⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ · ⟅ ⌈ send ⌉ ⟆)
  ≡ map traces→right-sided-intervals ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
    ·ᵣ map traces→right-sided-intervals ⟅ ⌈ send ⌉ ⟆
deadlines-add = refl
