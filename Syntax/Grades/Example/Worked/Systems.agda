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
-- There are seven: one between time intervals, and one for each of the --
-- six trace grades. Every trace projection measures a set of traces by  --
-- a duration, and each aggregates in the direction its endpoint is      --
-- *read* rather than in the direction it bounds -- so a disjunctive     --
-- endpoint takes the slowest or fastest member according to which way   --
-- its quantifier runs, and the one conjunctive endpoint in the          --
-- development, the subset floor, takes the slowest.                     --
--                                                                      --
-- Systems for the sub-trace-order grid are parked under `backup/`.      --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Systems where

open import Data.Product using (_,_)

open import Util.Equality

open import Syntax.Grades using (Grade; _→ᵍ_)

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

open import Data.Nat.Base using (ℕ; _≤_)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; eqᵢ; _·ᵢ_; _≾ᵢ_; ↑_; ∞; two-sided-intervals-with-⊤)
  renaming ([_,_,_] to mkᵢ; only_ to only²_)

open import Syntax.Grades.Example.Time.LeftSided
  using ([_,+∞⟩; _·ₒ_; _≾ₒ_; left-sided-intervals-with-⊤)
  renaming (only_ to onlyˡ_; ⊤ᵍ to ⊤ˡ)

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
  Op _≟ₒ_ costʰⁱ costʰⁱ-pos using (traces→right-sided-intervals)

open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
  using (_≾_; holds) renaming (only_ to onlyᵃ_; ⊤ᵍ to ⊤ᵃ; _·_ to _·ᵃ_)

-- a reading and six ticks' worth of work is a seven-tick deadline

budget-measured :
  map traces→right-sided-intervals (onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆) ≡ [0, 7 ]
budget-measured = refl

-- and a grade listing alternatives is measured by the slowest of them

alternatives-measured :
  map traces→right-sided-intervals
      (onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
  ≡ [0, 12 ]
alternatives-measured = refl

-- the unbounded grade becomes the deadline that is no deadline

unbounded-measured : map traces→right-sided-intervals ⊤ᵃ ≡ mkᵣ ∞
unbounded-measured = refl

-- what the projection forgets is which operations are permitted: a
-- bound naming a store and one budgeting the three ticks a store takes
-- become the same deadline, though only the first permits the store
-- outright

operations-forgotten :
  map traces→right-sided-intervals (onlyᵃ ⟅ ⌈ write ⌉ ⟆)
  ≡ map traces→right-sided-intervals (onlyᵃ ⟅ ⟨ 3 ⟩ ⟆)
operations-forgotten = refl

-- upstream those two are ordered one way and not the other, which the
-- deadline cannot see

store-within-three-ticks : onlyᵃ ⟅ ⌈ write ⌉ ⟆ ≾ onlyᵃ ⟅ ⟨ 3 ⟩ ⟆
store-within-three-ticks = holds

-- monotonicity: weakening a grade to a budget raises the deadline with
-- it, from four ticks to seven

deadline-rises :
  map traces→right-sided-intervals (onlyᵃ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
  ≾ᵣ map traces→right-sided-intervals (onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
deadline-rises =
  map-monotone traces→right-sided-intervals
               {onlyᵃ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆} {onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆} holds

-- and it is a monoid map: sequencing before or after measuring agrees

deadlines-add :
  map traces→right-sided-intervals
      (onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ·ᵃ onlyᵃ ⟅ ⌈ send ⌉ ⟆)
  ≡ map traces→right-sided-intervals (onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
    ·ᵣ map traces→right-sided-intervals (onlyᵃ ⟅ ⌈ send ⌉ ⟆)
deadlines-add = refl

------------------------------------------------------------------------
-- Forgetting the runs, keeping the guarantee
--
-- `System.Traces.Timed.LeftSided` measures a grade of guarantees by its
-- *fastest* one. The set is read disjunctively -- which listed trace
-- was covered is not known -- so all that is guaranteed about the time
-- is what the cheapest member takes.

open import Syntax.Grades.Example.System.Traces.Timed.LeftSided
  Op _≟ₒ_ costˡᵒ using (traces→left-sided-intervals)

open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
  using () renaming (holds to holdsᶜ)

-- a reading, two ticks' settling and a transmission guarantee seven
-- ticks, the two operations credited at their best case

guarantee-measured :
  map traces→left-sided-intervals ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≡ [ 7 ,+∞⟩
guarantee-measured = refl

-- and a grade listing alternatives is measured by the fastest of them,
-- which is the reverse of what the cap's projection does

alternatives-measured-below :
  map traces→left-sided-intervals
      ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  ≡ [ 1 ,+∞⟩
alternatives-measured-below = refl

-- what the projection forgets is again which operations occurred: a
-- guarantee that a store happened and one that two ticks passed
-- become the same lower bound, though only the first guarantees the
-- store

stores-forgotten :
  map traces→left-sided-intervals ⟅ ⌈ write ⌉ ⟆
  ≡ map traces→left-sided-intervals ⟅ ⟨ 2 ⟩ ⟆
stores-forgotten = refl

-- monotonicity: dropping to the reading alone drops the guarantee from
-- seven ticks to one

guarantee-falls :
  map traces→left-sided-intervals ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  ≾ₒ map traces→left-sided-intervals ⟅ ⌈ read ⌉ ⟆
guarantee-falls =
  map-monotone traces→left-sided-intervals
               {⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} {⟅ ⌈ read ⌉ ⟆} holdsᶜ

-- and it is a monoid map: sequencing before or after measuring agrees

guarantees-add :
  map traces→left-sided-intervals (⟅ ⌈ read ⌉ ⟆ · ⟅ ⌈ send ⌉ ⟆)
  ≡ map traces→left-sided-intervals ⟅ ⌈ read ⌉ ⟆
    ·ₒ map traces→left-sided-intervals ⟅ ⌈ send ⌉ ⟆
guarantees-add = refl

------------------------------------------------------------------------
-- Keeping both endpoints
--
-- `System.Traces.Timed.TwoSided` is the pair of the two projections above,
-- and lands in a time interval only because the grade's coherence field
-- makes the fastest guarantee no slower than the slowest allowance.

open import Data.Unit using (tt)

open import Syntax.Grades.Example.System.Traces.Timed.TwoSided
  Op _≟ₒ_ costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos using (two-sided-traces→intervals)

open import Syntax.Grades.Example.Worked.Traces.Timed.TwoSided
  using (exact; _·ᵗˢ_) renaming ([_,_,_] to ⟪_,_,_⟫; holds to holdsᵗˢ)

-- a contract that guarantees a reading and permits it six ticks' more
-- work becomes the window between one tick and seven

contract-measured :
  map two-sided-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ⟆ , onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ⟫
  ≡ [ 1 , 7 , ≤! ]
contract-measured = refl

-- listing alternatives widens the window at both ends at once, each end
-- aggregating its own way

alternatives-measured-both :
  map two-sided-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆
      , onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ , tt ⟫
  ≡ [ 1 , 12 , ≤! ]
alternatives-measured-both = refl

-- a grade whose two endpoints coincide still becomes a window, the two
-- cost models pulling its ends apart: a reading and a store are certain
-- to take three ticks and may take four

exact-measured : map two-sided-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
               ≡ [ 3 , 4 , ≤! ]
exact-measured = refl

-- monotonicity: a computation known to take a reading and a store sits
-- inside the contract's window

window-contains :
  map two-sided-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
  ≾ᵢ map two-sided-traces→intervals
         ⟪ ⟅ ⌈ read ⌉ ⟆ , onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ⟫
window-contains =
  map-monotone two-sided-traces→intervals
               {exact (⌈ read ⌉ ∙ ⌈ write ⌉)}
               {⟪ ⟅ ⌈ read ⌉ ⟆ , onlyᵃ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ⟫}
               (holdsᵗˢ _ _)

-- and it is a monoid map: sequencing before or after measuring agrees

windows-add :
  map two-sided-traces→intervals (exact ⌈ read ⌉ ·ᵗˢ exact ⌈ send ⌉)
  ≡ map two-sided-traces→intervals (exact ⌈ read ⌉)
    ·ᵢ map two-sided-traces→intervals (exact ⌈ send ⌉)
windows-add = refl

------------------------------------------------------------------------
-- The subset grades, and where they read a set differently
--
-- The subset projections measure by the slowest member at *every*
-- endpoint. Above that is the usual reason -- any listed run may occur,
-- so the deadline must cover the slowest. Below it is the opposite
-- reason: the subset floor is read conjunctively, every listed run
-- being separately demanded, so the guarantee is what the slowest of
-- them takes.
--
-- The timed floor, read disjunctively, takes the fastest instead. Same
-- source set, opposite aggregation -- the direction follows the reading
-- of the set, not the side of the interval.
--
-- The two floors do not share a target: the subset floor's greatest
-- grade demands nothing and absorbs, and no projection preserving both
-- `⊤` and `_·_` takes an absorbing top to `[ 0 ,+∞⟩`, which is the
-- intervals' unit. So it lands in the intervals with a top adjoined,
-- and the timed floor, whose own greatest grade is its unit, lands in
-- the plain ones.

open import Syntax.Grades.Example.System.Traces.Subsets.RightSided
  Op _≟ₒ_ costʰⁱ using (subsets→right-sided-intervals)
open import Syntax.Grades.Example.System.Traces.Subsets.LeftSided
  Op _≟ₒ_ costˡᵒ using (subsets→left-sided-intervals)
open import Syntax.Grades.Example.System.Traces.Subsets.TwoSided
  Op _≟ₒ_ costˡᵒ costʰⁱ cost-≤ using (subsets→intervals)

open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
  using () renaming (holds to holdsˢʰ; only_ to onlyᵖ_)
open import Syntax.Grades.Example.Worked.Traces.Subsets.LeftSided
  using () renaming (holds to holdsˢˡ; only_ to onlyᵈ_; ⊤ᵍ to ⊤ᵈ)
open import Syntax.Grades.Example.Worked.Traces.Subsets.TwoSided
  using (branching; contract; _·ᴵ_) renaming (holds to holdsˢᵇ)

-- the two branches take one tick and three-to-four ticks

the-branches : NeTraces
the-branches = ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆

-- above, the deadline is the slower branch at its worst case

cap-measured : map subsets→right-sided-intervals (onlyᵖ the-branches) ≡ [0, 4 ]
cap-measured = refl

-- below, so is the guarantee -- because both branches are demanded --
-- but read at the best case

-- and the resource grade is one of the extended left-sided intervals,
-- its `⊤ᵍ` receiving the floor's "nothing is demanded"

floor-measured :
  map subsets→left-sided-intervals (onlyᵈ the-branches) ≡ onlyˡ [ 3 ,+∞⟩
floor-measured = refl

-- where the timed floor, listing alternatives rather than demands,
-- guarantees only what the faster of them takes

timed-floor-measured :
  map traces→left-sided-intervals the-branches ≡ [ 1 ,+∞⟩
timed-floor-measured = refl

-- monotonicity, above: permitting a further run raises the deadline

cap-deadline-rises :
  map subsets→right-sided-intervals (onlyᵖ ⟅ ⌈ read ⌉ ⟆)
  ≾ᵣ map subsets→right-sided-intervals (onlyᵖ the-branches)
cap-deadline-rises =
  map-monotone subsets→right-sided-intervals
               {onlyᵖ ⟅ ⌈ read ⌉ ⟆} {onlyᵖ the-branches} holdsˢʰ

-- and below: forgetting a demanded run lowers the guarantee

floor-guarantee-falls :
  Grade._≾_ left-sided-intervals-with-⊤
            (map subsets→left-sided-intervals (onlyᵈ the-branches))
            (map subsets→left-sided-intervals (onlyᵈ ⟅ ⌈ read ⌉ ⟆))
floor-guarantee-falls =
  map-monotone subsets→left-sided-intervals
               {onlyᵈ the-branches} {onlyᵈ ⟅ ⌈ read ⌉ ⟆} holdsˢˡ

-- the floor's greatest grade demands nothing, and lands on the target's
-- own greatest grade

floor-top-measured : map subsets→left-sided-intervals ⊤ᵈ ≡ ⊤ˡ
floor-top-measured = refl

-- the two-sided projection is the pair, and the window it lands in is
-- non-degenerate because the grade's coherence field is

subset-contract-measured :
  map subsets→intervals contract ≡ only² [ 1 , 4 , ≤! ]
subset-contract-measured = refl

branching-inside-the-contract :
  Grade._≾_ two-sided-intervals-with-⊤
            (map subsets→intervals branching)
            (map subsets→intervals contract)
branching-inside-the-contract =
  map-monotone subsets→intervals {branching} {contract} (holdsˢᵇ _ _)

-- and it is a monoid map at both endpoints

subset-windows-add :
  map subsets→intervals (branching ·ᴵ contract)
  ≡ Grade._·_ two-sided-intervals-with-⊤
              (map subsets→intervals branching)
              (map subsets→intervals contract)
subset-windows-add = refl
