------------------------------------------------------------------------
-- Worked instances of the grade systems.                              --
--                                                                     --
-- A grade system pairs effect grades (what a computation may do) with --
-- resource grades (what is thereby guaranteed about time) and a       --
-- monoid map `∣_∣ᵉ` projecting the first onto the second. Reading the --
-- projection tells you what the resource grade may forget.            --
--                                                                     --
-- Each section computes the projection on the sensor node's own       --
-- grades and then exercises its monotonicity: an ordering between two --
-- effect grades must still hold between their images.                 --
--                                                                     --
-- There are five: one between time intervals, and one for each of     --
-- the four trace grades. Every trace projection measures a set of     --
-- traces by a duration: the sets are read disjunctively -- which      --
-- listed trace was taken is not known -- so a cap has to cover the    --
-- slowest member and a floor may promise only the fastest.            --
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
-- `IntervalsToLeftSidedIntervals` keeps the lower endpoint alone: the
-- effect grade says the uplink takes between 7 and 9 ticks, the
-- resource grade only that at least 7 have passed.

open import Data.Nat.Base using (ℕ; _≤_)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; eqᵢ; _·ᵢ_; _≾ᵢ_; ↑_; ∞)
  renaming ([_,_,_] to mkᵢ)

open import Syntax.Grades.Example.Time.LeftSided
  using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

-- every window below has a finite upper endpoint

[_,_,_] : (m n : ℕ) → m ≤ n → Interval∞
[ m , n , p ] = mkᵢ m (↑ n) p

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

-- monotonicity: enlarging the window to `[ 5 , 12 ]` weakens the lower
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
-- `System.Traces.Timed.RightSided` measures a grade of trace bounds by its
-- slowest bound. The effect grade still says which runs are permitted
-- and which operations they may perform; the resource grade keeps only
-- how long they may take.

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

------------------------------------------------------------------------
-- Forgetting the runs, keeping the guarantee
--
-- `System.Traces.Timed.LeftSided` measures a grade of guarantees by its
-- *fastest* one. The set is read disjunctively -- which listed trace
-- was covered is not known -- so all that is guaranteed about the time
-- is what the cheapest member takes.

open import Syntax.Grades.Example.System.Traces.Timed.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ using (traces→left-sided-intervals)

open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
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

------------------------------------------------------------------------
-- Keeping both endpoints
--
-- `System.Traces.Timed.TwoSided` is the pair of the two projections above,
-- and lands in a time interval only because the grade's coherence field
-- makes the fastest guarantee no slower than the slowest allowance.

open import Data.Unit using (tt)

open import Syntax.Grades.Example.System.Traces.Timed.TwoSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos
  using (two-sided-traces→intervals)

open import Syntax.Grades.Example.Worked.Traces.Timed.TwoSided
  using (exact; _·ᵗˢ_) renaming ([_,_,_] to ⟪_,_,_⟫; holds to holdsᵗˢ)

-- a contract that guarantees a reading and permits it six ticks' more
-- work becomes the window between one tick and seven

contract-measured :
  map two-sided-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ , tt ⟫
  ≡ [ 1 , 7 , ≤! ]
contract-measured = refl

-- listing alternatives enlarges the window at both ends at once, each end
-- aggregating its own way

alternatives-measured-both :
  map two-sided-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ˡᵒ
      , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ʰⁱ , tt ⟫
  ≡ [ 1 , 12 , ≤! ]
alternatives-measured-both = refl

-- a grade whose two endpoints coincide still becomes a window, the two
-- cost models pulling its ends apart: a reading and a store are certain
-- to take three ticks and may take four

exact-measured :
  map two-sided-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
               ≡ [ 3 , 4 , ≤! ]
exact-measured = refl

-- monotonicity: a computation known to take a reading and a store sits
-- inside the contract's window

window-contains :
  map two-sided-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
  ≾ᵢ map two-sided-traces→intervals
         ⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ , tt ⟫
window-contains =
  map-monotone two-sided-traces→intervals
               {exact (⌈ read ⌉ ∙ ⌈ write ⌉)}
               {⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ , tt ⟫}
               (holdsᵗˢ _ _)

-- and it is a monoid map: sequencing before or after measuring agrees

windows-add :
  map two-sided-traces→intervals (exact ⌈ read ⌉ ·ᵗˢ exact ⌈ send ⌉)
  ≡ map two-sided-traces→intervals (exact ⌈ read ⌉)
    ·ᵢ map two-sided-traces→intervals (exact ⌈ send ⌉)
windows-add = refl

------------------------------------------------------------------------
-- The subset cap, beside the timed floor
--
-- At the subset order nothing is approximated: the grade lists the runs
-- outright, and the deadline is the slowest of them at its worst case.
-- The timed floor, on the same two runs, takes the fastest instead --
-- which side the endpoint bounds is what fixes the direction.

open import Syntax.Grades.Example.System.Traces.Subsets.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ using (subsets→right-sided-intervals)

open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
  using (permitting_) renaming (holds to holdsˢʰ)

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
