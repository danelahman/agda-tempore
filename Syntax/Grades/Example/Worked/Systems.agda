------------------------------------------------------------------------
-- Worked instances of the four grade systems.                         --
--                                                                     --
-- A grade system pairs effect grades -- what a computation may do --   --
-- with resource grades -- what is thereby guaranteed about time -- and --
-- a monoid map `∣_∣ᵉ` projecting the first onto the second. Reading    --
-- the projection tells you what the resource grade may forget, and     --
-- each of the four forgets something different:                        --
--                                                                     --
--   intervals  -> left-sided    the upper bound                        --
--   trace sets -> restricted    the operations off a sub-alphabet      --
--   trace sets -> intervals     the runs, keeping only their window    --
--   trace sets -> cost-aware    nothing; it coarsens the order instead --
--                                                                     --
-- Each section computes the projection on the sensor node's own grades --
-- and then exercises its monotonicity: an ordering between two effect  --
-- grades must still hold between their images.                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Systems where

open import Data.Bool using (Bool; true; false)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse; fromWitness)

open import Syntax.Grades using (_→ᵍ_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations
open import Syntax.Grades.Example.Worked.Spec using (spec)

open _→ᵍ_ using (map; map-monotone)

------------------------------------------------------------------------
-- Forgetting the upper bound
--
-- `IntervalsToLeftSidedIntervals` keeps the lower endpoint alone. The
-- effect grade says the uplink takes between 7 and 9 ticks; the
-- resource grade says only that at least 7 have passed -- which is what
-- a box modality needs, since it is about data having become available,
-- not about a deadline.

open import Syntax.Grades.Example.Interval.TwoSided
  using ([_,_,_]; eqᵢ; _·ᵢ_; _≾ᵢ_)

open import Syntax.Grades.Example.Interval.LeftSided
  using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

open import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals
  using (tsi→lsi)

open import Syntax.Grades.Example.Worked.Intervals
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
-- Forgetting the runs, keeping their window
--
-- `TracesToTimeIntervals` measures a set of traces against `opTime` and
-- returns the interval between its best- and worst-case duration. The
-- effect grade still says *which* runs there are; the resource grade
-- keeps only how long they may take.

open import Syntax.Grades.Example.System.TracesToTimeIntervals spec
  using (mapᵢ; traces→time-intervals)

open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
  using () renaming (_≾_ to _≾ⁱ_)

open import Syntax.Grades.Example.Worked.TraceSets using (module Inclusion)
open import Syntax.Grades.Example.Worked.TraceIntervals using (module LeftSided)

-- the node either polls or does the full uplink

did-uplink : NeTraces
did-uplink = ⟅ uplink ⟆

-- the node either polls or does the full uplink, and offering only the
-- uplink is an inclusion into that

poll-or-uplink : NeTraces
poll-or-uplink = ⟅ poll ∣ uplink ⟆

uplink-listed : did-uplink ≾ⁱ poll-or-uplink
uplink-listed = Inclusion.holds

-- the uplink alone spans exactly the window `Worked.Intervals` names:
-- 1 + 2 + 4 at the bottom, 1 + 2 + 6 at the top

uplink-spans : mapᵢ opTime did-uplink ≡ uplink-window
uplink-spans = eqᵢ refl refl

-- adding the much faster `poll` run drops the lower endpoint to 1 and
-- leaves the upper one alone

both-span : mapᵢ opTime poll-or-uplink ≡ [ 1 , 9 , ≤! ]
both-span = eqᵢ refl refl

-- which is monotonicity at work: the inclusion above becomes the
-- containment `[ 7 , 9 ] ⊆ [ 1 , 9 ]`

both-span-mono : mapᵢ opTime did-uplink ≾ᵢ mapᵢ opTime poll-or-uplink
both-span-mono =
  map-monotone (traces→time-intervals opTime) {did-uplink} {poll-or-uplink}
               uplink-listed

-- the projection loses the runs themselves: a grade offering a poll or
-- an uplink, and one offering a one-tick or a nine-tick wait, span the
-- same window and are indistinguishable downstream

window-forgets-runs :
  mapᵢ opTime poll-or-uplink ≡ mapᵢ opTime (⟅ ⟨ 1 ⟩ ∣ ⟨ 9 ⟩ ⟆)
window-forgets-runs = eqᵢ refl refl

------------------------------------------------------------------------
-- Forgetting the operations off a sub-alphabet
--
-- `TracesToRestrictedTraces` restricts every run to the operations a
-- predicate admits. Take that predicate to be "uses the radio": the
-- resource grades then account for radio traffic and for time, and are
-- blind to everything the node does locally.

radio : Op → Bool
radio read  = false
radio write = false
radio send  = true

open import Syntax.Grades.Traces.Restriction Op _≟ₒ_ radio
  using (Op'; restrict-trace)

open import Syntax.Grades.Traces.Sets Op'
  using () renaming (ε to εᴿ; ⟨_⟩ to ⟨_⟩ᴿ; ⌈_⌉ to ⌈_⌉ᴿ; _∙_ to _∙ᴿ_;
                     traces to tracesᴿ)

open import Syntax.Grades.Example.System.TracesToRestrictedTraces spec
  using (traces→subset-traces)

-- the uplink keeps its idle time and its transmission, and loses the
-- sensor read that preceded them

uplink-restricted : restrict-trace uplink ≡ ⟨ 2 ⟩ᴿ ∙ᴿ ⌈ send , tt ⌉ᴿ
uplink-restricted = refl

-- a purely local run becomes invisible: nothing of it is on-alphabet

poll-restricted : restrict-trace poll ≡ εᴿ
poll-restricted = refl

logged-restricted : restrict-trace logged ≡ εᴿ
logged-restricted = refl

-- so the two local runs are identified, and a grade that distinguishes
-- them projects to one that does not

local-runs-merge : restrict-trace poll ≡ restrict-trace logged
local-runs-merge = refl

-- at the level of grades, `{ poll , uplink }` becomes
-- `{ ε , ⟨ 2 ⟩ ∙ ⌈ send ⌉ }`

restricted-grade :
  tracesᴿ (map (traces→subset-traces radio) poll-or-uplink)
  ≡ εᴿ ∷ (⟨ 2 ⟩ᴿ ∙ᴿ ⌈ send , tt ⌉ᴿ) ∷ []
restricted-grade = refl

------------------------------------------------------------------------
-- Forgetting nothing, comparing more coarsely
--
-- `TracesToCostAwareTraces` is the identity on carriers: effect and
-- resource grades are the very same sets of traces. All it does is
-- reinterpret the order, from inclusion to the cost-aware sub-trace
-- lift. Monotonicity is then the statement that inclusion is contained
-- in that lift -- and `Worked.TraceSets` row 1 shows the containment is
-- strict, so this projection really does coarsen.

open import Syntax.Grades.Example.System.TracesToCostAwareTraces spec
  using (traces→cost-aware-traces; fast-traces→slow-traces)

open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ˢ_)

-- the carrier is untouched

cost-aware-identity : map (traces→cost-aware-traces cost) poll-or-uplink
                    ≡ poll-or-uplink
cost-aware-identity = refl

-- and every inclusion survives as a sub-trace ordering

inclusion-survives : did-uplink ≾ˢ poll-or-uplink
inclusion-survives =
  map-monotone (traces→cost-aware-traces cost)
               {did-uplink} {poll-or-uplink} uplink-listed

------------------------------------------------------------------------
-- Reinterpreting one cost model as another
--
-- The cost-aware grades form a family indexed by the execution times.
-- Cheaper operations are easier to fit inside a schedule, so lowering
-- the cost widens the order, and the identity on sets of traces is a
-- grade morphism from the slow model to the fast one. `cost` is `slow`,
-- so `_≾ˢ_` above is already the slow order.

open import Syntax.Grades.Traces.Subtrace Op fast
  using () renaming (_≼_ to _≼ᶠ_; module DecSubtrace to DecFast)

open import Syntax.Grades.Traces.Subtrace Op slow
  using () renaming (_≼_ to _≼ˢˡ_; module DecSubtrace to DecSlow)

open DecFast _≟ₒ_ using () renaming (_≼?_ to _≼ᶠ?_)
open DecSlow _≟ₒ_ using () renaming (_≼?_ to _≼ˢˡ?_)

open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ fast
  using () renaming (_≾_ to _≾ᶠ_)

-- An elapsed write banks its execution time -- 2 ticks under `fast`,
-- 3 under `slow` -- so a demand for three ticks is discharged by a
-- write only in the dearer model.

write-banks-two : ⟨ 2 ⟩ ≼ᶠ ⌈ write ⌉
write-banks-two = toWitness {a? = ⟨ 2 ⟩ ≼ᶠ? ⌈ write ⌉} tt

write-banks-no-three-fast : ¬ (⟨ 3 ⟩ ≼ᶠ ⌈ write ⌉)
write-banks-no-three-fast = toWitnessFalse {a? = ⟨ 3 ⟩ ≼ᶠ? ⌈ write ⌉} tt

write-banks-three-slow : ⟨ 3 ⟩ ≼ˢˡ ⌈ write ⌉
write-banks-three-slow = toWitness {a? = ⟨ 3 ⟩ ≼ˢˡ? ⌈ write ⌉} tt

-- so the dearer model has the wider order, and the morphism carries a
-- cheap-model ordering into it

meets-fast : {P Q : NeTraces}
           → ({t : Trace} → t ∈ traces P → Any (_≼ᶠ t) (traces Q)) → P ≾ᶠ Q
meets-fast f t m = fromWitness (f (toWitness m))

did-write demand-two : NeTraces
did-write  = ⟅ ⌈ write ⌉ ⟆
demand-two = ⟅ ⟨ 2 ⟩ ⟆

write-fast : did-write ≾ᶠ demand-two
write-fast =
  meets-fast {did-write} {demand-two} λ { (here refl) → here write-banks-two }

dearer-keeps-order : did-write ≾ˢ demand-two
dearer-keeps-order =
  map-monotone (fast-traces→slow-traces fast slow fast≤slow)
               {did-write} {demand-two} write-fast

-- the converse is not a morphism: three ticks are discharged by a write
-- in the slow model and not in the fast one

slow-order-is-wider : ¬ (⟨ 3 ⟩ ≼ᶠ ⌈ write ⌉)
slow-order-is-wider = write-banks-no-three-fast
