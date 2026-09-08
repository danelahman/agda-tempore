------------------------------------------------------------------------
-- The mixed column over the time-strict sub-trace order.              --
--                                                                     --
-- `Worked.Traces.Subtrace.Mixed` is about the lift axis: what a Smyth  --
-- floor under a Hoare cap says together. This module is about the      --
-- other axis, and takes the same kinds of claim across it.            --
--                                                                     --
-- One scenario runs through all of it: the radio's duty cycle. The     --
-- node may not transmit twice in quick succession, so                 --
--                                                                     --
--   ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉                                       --
--                                                                     --
-- demands four ticks *between* two transmissions. Two runs do the same --
-- housekeeping -- store the reading, take the next one -- and differ   --
-- only in whether they do it in the gap or before the first            --
-- transmission:                                                       --
--                                                                     --
--   ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉      in the gap        --
--   ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉      up front          --
--                                                                     --
-- Under `cost` -- read 1, write 3, send 6 -- all three take sixteen    --
-- ticks, and the housekeeping is worth exactly the four the duty cycle --
-- asks for. So no measure of elapsed time separates these runs; only   --
-- where the time falls does.                                          --
--                                                                     --
-- Leniently both runs meet the demand, time banked anywhere paying a   --
-- delay demanded anywhere later. Time-strictly only the first does:    --
-- banked time never crosses a matched operation, so housekeeping done  --
-- before the first transmission leaves the radio transmitting back to  --
-- back. That is what a duty cycle means, and what the time-strict      --
-- order is for.                                                       --
--                                                                     --
-- What the mixed grade adds is where the failure lands. It is not only --
-- a coercion that is lost but the *consistency field*: a pair of sets  --
-- that is an interval over the lenient order need not be one at all    --
-- over the time-strict order, so the grade cannot be written down.     --
-- Listing a weaker demand alongside repairs it, the floor's members    --
-- being read disjunctively.                                           --
--                                                                     --
-- The sets themselves are the same in both columns -- the carrier and  --
-- the monoid do not consult the order, which `sequencing-agrees`       --
-- checks across the two columns -- so everything the axis changes is   --
-- about which coercions between those sets exist. The same two-element --
-- set that trims to one member at each endpoint leniently is           --
-- irreducible time-strictly, being a chain in one column and an        --
-- antichain in the other.                                             --
--                                                                     --
-- The last two sections read the order as the typing rules do: an      --
-- effect grade whose cap `coerce` may widen in one column and not the  --
-- other, and a box that one and the same elapsed grade opens in one    --
-- column and not the other.                                           --
--                                                                     --
-- As in the lenient module, every run is written out in full in every  --
-- claim, and every claim is closed by running a decision procedure.    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.SubtraceTimed.Mixed where

open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

-- the mixed grade over each of the two orders

open import Syntax.Grades.Example.Traces.Subtrace.Mixed.TwoSided Op _≟ₒ_ cost
  using (lo)
  renaming (MixedInterval to Interval; [_,_,_] to mk; _◇ˢ_ to _◇ˢ_;
            ◇ˢ-refl to ◇ˢ-refl; _·ᵐⁱ_ to _·ᵐ_;
            _≾ᵐⁱ_ to _≾ᵐ_; _≾ᵐⁱ?_ to _≾ᵐ?_)
open import Syntax.Grades.Example.Traces.SubtraceTimed.Mixed.TwoSided Op _≟ₒ_ cost
  using ()
  renaming (MixedInterval to Intervalᵗ; [_,_,_] to mkᵗ; lo to loᵗ;
            _◇ˢ_ to _◇ˢᵗ_; ◇ˢ-refl to ◇ˢᵗ-refl; _·ᵐⁱ_ to _·ᵐᵗ_;
            _≾ᵐⁱ_ to _≾ᵐᵗ_; _≾ᵐⁱ?_ to _≾ᵐᵗ?_)

-- and its two endpoints over each, which is where the columns disagree

open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.LeftSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶠ_; _≾?_ to _≾ᶠ?_)
open import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.LeftSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶠᵗ_; _≾?_ to _≾ᶠᵗ?_)
open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.RightSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶜ_; _≾?_ to _≾ᶜ?_)
open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.RightSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶜᵗ_; _≾?_ to _≾ᶜᵗ?_)

holdsᶠ : {P Q : NeTraces} {p : True (P ≾ᶠ? Q)} → P ≾ᶠ Q
holdsᶠ {p = p} = toWitness p

failsᶠ : {P Q : NeTraces} {p : False (P ≾ᶠ? Q)} → ¬ (P ≾ᶠ Q)
failsᶠ {p = p} = toWitnessFalse p

holdsᶠᵗ : {P Q : NeTraces} {p : True (P ≾ᶠᵗ? Q)} → P ≾ᶠᵗ Q
holdsᶠᵗ {p = p} = toWitness p

failsᶠᵗ : {P Q : NeTraces} {p : False (P ≾ᶠᵗ? Q)} → ¬ (P ≾ᶠᵗ Q)
failsᶠᵗ {p = p} = toWitnessFalse p

holdsᶜ : {P Q : NeTraces} {p : True (P ≾ᶜ? Q)} → P ≾ᶜ Q
holdsᶜ {p = p} = toWitness p

failsᶜ : {P Q : NeTraces} {p : False (P ≾ᶜ? Q)} → ¬ (P ≾ᶜ Q)
failsᶜ {p = p} = toWitnessFalse p

failsᶜᵗ : {P Q : NeTraces} {p : False (P ≾ᶜᵗ? Q)} → ¬ (P ≾ᶜᵗ Q)
failsᶜᵗ {p = p} = toWitnessFalse p

holdsᵐ : (i j : Interval) {p : True (i ≾ᵐ? j)} → i ≾ᵐ j
holdsᵐ i j {p} = toWitness p

holdsᵐᵗ : (i j : Intervalᵗ) {p : True (i ≾ᵐᵗ? j)} → i ≾ᵐᵗ j
holdsᵐᵗ i j {p} = toWitness p

failsᵐᵗ : (i j : Intervalᵗ) {p : False (i ≾ᵐᵗ? j)} → ¬ (i ≾ᵐᵗ j)
failsᵐᵗ i j {p} = toWitnessFalse p

------------------------------------------------------------------------
-- The duty cycle, on one run
--
-- Housekeeping done in the gap is worth its execution time there, and
-- the same housekeeping done up front is worth nothing there -- which
-- is the whole of the difference between the two columns.

housekeeping-in-the-gap :
  ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᶠᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
housekeeping-in-the-gap = holdsᶠᵗ

housekeeping-up-front :
  ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᶠ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
housekeeping-up-front = holdsᶠ

housekeeping-up-front-not-timed :
  ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ᶠᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆)
housekeeping-up-front-not-timed = failsᶠᵗ

-- and a gap that is merely shorter than the duty cycle fails in both
-- columns: the store alone is worth three ticks, not four

store-alone-is-too-short :
  ¬ (⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ᶠ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆)
store-alone-is-too-short = failsᶠ

------------------------------------------------------------------------
-- So the grade itself is lost, not just a coercion into it
--
-- Over the lenient order the duty cycle sits inside the up-front run,
-- so the pair is an interval: a grade demanding the duty cycle and
-- permitting that run.

contract : Interval
contract = mk ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
              ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt

-- time-strictly that same pair has no consistency witness: what the
-- cap permits does not meet what the floor demands, so there is no run
-- the grade admits and the grade cannot be written down

inconsistent-timed :
  ¬ (traces ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
     ◇ˢᵗ traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
inconsistent-timed ()

-- offering "at least one transmission" as a second demand makes the
-- pair an interval again, over either order, and the up-front run meets
-- that

repaired : Intervalᵗ
repaired = mkᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ⟆
               ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt

up-front-meets-the-repair :
  mkᵗ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
      ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
      (◇ˢᵗ-refl ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
  ≾ᵐᵗ repaired
up-front-meets-the-repair = holdsᵐᵗ _ _

------------------------------------------------------------------------
-- Sequencing is the same operation in both columns
--
-- The carrier is a set of traces and the monoid is the language product
-- on it; neither consults the order. A phase that either takes a
-- reading or stores one, followed by one that either transmits or idles
-- a tick, has the same four runs whichever column the grade lives in.

sequencing-agrees :
  traces (loᵗ ( mkᵗ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ tt
              ·ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ tt))
  ≡ traces (lo  ( mk  ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ tt
              ·ᵐ  mk  ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ tt))
sequencing-agrees = refl

------------------------------------------------------------------------
-- A set that trims leniently and not time-strictly
--
-- `{ duty cycle , the up-front run }` is a chain over the lenient
-- order, the duty cycle being met by that run. As a floor the run is
-- then the redundant member and the set trims to the duty cycle alone;
-- as a cap the duty cycle is redundant and it trims to the run.
-- Time-strictly the two are incomparable and neither trimming is
-- available: one and the same pair of traces is a chain in one column
-- and an antichain in the other.

floor-trims :
  ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᶠ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
floor-trims = holdsᶠ

floor-trims-not-timed :
  ¬ (⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉
     ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ᶠᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆)
floor-trims-not-timed = failsᶠᵗ

cap-trims :
  ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᶜ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
cap-trims = holdsᶜ

cap-trims-not-timed :
  ¬ (⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉
     ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ᶜᵗ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
cap-trims-not-timed = failsᶜᵗ

-- keeping the other member instead is available in neither column: the
-- run performs a store and a read, which the duty cycle never mentions

floor-other-way :
  ¬ (⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉
     ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ᶠ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
floor-other-way = failsᶠ

cap-other-way :
  ¬ (⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉
     ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ᶜ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆)
cap-other-way = failsᶜ

------------------------------------------------------------------------
-- Two possible runs against one demand, and the repair
--
-- A computation that does its housekeeping in the gap or up front,
-- depending on what it finds. Leniently both runs observe the duty
-- cycle, so a single listed demand carries the pair; time-strictly only
-- the first does, and the floor has to offer a weaker demand as well.

both-runs-lenient :
  ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
  ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᶠ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
both-runs-lenient = holdsᶠ

both-runs-timed :
  ¬ (⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
     ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ᶠᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆)
both-runs-timed = failsᶠᵗ

both-runs-repaired :
  ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
  ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᶠᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ⟆
both-runs-repaired = holdsᶠᵗ

------------------------------------------------------------------------
-- As an effect grade: a coercion the axis costs
--
-- A cap is a schedule the computation must stay within, and widening
-- one replaces a schedule by a more permissive one. Start from the
-- duty-cycled schedule and widen it to a schedule that fills the gap
-- with housekeeping, and then to one that does the housekeeping up
-- front. The first is more permissive in either column; the second only
-- leniently, since a schedule transmitting back to back does not permit
-- the run the duty cycle asks for.

widening-into-the-gap :
  mkᵗ ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ tt
widening-into-the-gap = holdsᵐᵗ _ _

widening-up-front :
  mk ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐ mk ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
widening-up-front = holdsᵐ _ _

widening-up-front-not-timed :
  ¬ (mkᵗ ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆ tt
     ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt)
widening-up-front-not-timed = failsᵐᵗ _ _

-- the duty cycle is what the axis turns on: drop the delay from the
-- schedule and the same widening holds in either column

widening-without-the-duty-cycle :
  mkᵗ ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
widening-without-the-duty-cycle = holdsᵐᵗ _ _

-- dropping the floor asks nothing of when time was spent, and is
-- available in either column

dropping-the-floor-is-free :
  mkᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ⟆ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆ tt
dropping-the-floor-is-free = holdsᵐᵗ _ _

-- the same contrast with alternatives at every endpoint at once: a
-- computation that either transmits twice or only takes a reading,
-- whose cap is widened at the transmitting schedule alone

widening-one-of-two-schedules :
  mk ⟅ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
     ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆ tt
  ≾ᵐ mk ⟅ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
        ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆ tt
widening-one-of-two-schedules = holdsᵐ _ _

widening-one-of-two-schedules-not-timed :
  ¬ (mkᵗ ⟅ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
         ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆ tt
     ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
             ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆ tt)
widening-one-of-two-schedules-not-timed = failsᵐᵗ _ _

------------------------------------------------------------------------
-- As a resource grade: a box the axis closes
--
-- A box holding the radio's permission to transmit again: ready once
-- the duty cycle has been observed, and open to either way of arranging
-- the housekeeping.
--
--   [ { ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ }
--   , { ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
--     , ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ } ]
--
-- Its cap admits both runs, so the readiness half decides -- and the
-- two runs take sixteen ticks apiece, so nothing about how much time
-- elapsed could decide it.

in-the-gap-opens-it :
  mkᵗ ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
      ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
          ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
          ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
in-the-gap-opens-it = holdsᵐᵗ _ _

up-front-opens-it-leniently :
  mk ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐ mk ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
        ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
        ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
up-front-opens-it-leniently = holdsᵐ _ _

up-front-does-not-open-it-timed :
  ¬ (mkᵗ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
         ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
     ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ⟆
             ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
             ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt)
up-front-does-not-open-it-timed = failsᵐᵗ _ _

-- the elapsed side is universal, so a computation that may do either
-- opens the box only when both of its runs do -- and with alternatives
-- at every endpoint of both grades. A second, laxer duty cycle on the
-- floor does not help: the up-front run spends nothing in the gap, so
-- no demand naming one is met.

either-way-opens-it-leniently :
  mk ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
     ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
     ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐ mk ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ∙ ⌈ send ⌉ ⟆
        ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
        ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
either-way-opens-it-leniently = holdsᵐ _ _

either-way-does-not-timed :
  ¬ (mkᵗ ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
         ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
         ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
         ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
     ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ∙ ⌈ send ⌉ ⟆
             ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
             ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt)
either-way-does-not-timed = failsᵐᵗ _ _

-- what does help is a demand naming no gap at all, and the box weakens
-- into one both runs open, every endpoint still listing alternatives

weaker-box-opens-either-way :
  mkᵗ ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
      ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
      ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
      ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
  ≾ᵐᵗ mkᵗ ⟅ ⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
          ⟅ ⌈ send ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
          ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ tt
weaker-box-opens-either-way = holdsᵐᵗ _ _
