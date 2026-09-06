------------------------------------------------------------------------
-- Worked instances of the upper-lift column.                          --
--                                                                     --
-- `Grades.Example.Traces.UpperLift`: the same sub-trace matching as    --
-- `LowerLift`, but quantified over the other set of the pair. On       --
-- singleton grades the two columns agree, so the examples below are    --
-- chosen to sit either side of that: first the singletons they share,  --
-- then the pairs on which they disagree, each stated against both      --
-- orders so the disagreement is checked rather than asserted.         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.UpperLift where

open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost
  using (≽ˢ-refl; _≽ˢ?_)

------------------------------------------------------------------------
-- A floor under what must have happened
--
-- `UpperLift.LeftSided`, `traces Q ≽ˢ traces P`. The grade lists
-- alternative demands and a run discharges it by covering *one* of
-- them, so weakening may offer further alternatives.

module LeftSided where

  open import Syntax.Grades.Example.Traces.UpperLift.LeftSided Op _≟ₒ_ cost
    using (upper-lift-left-sided; _≾_; _≾?_) public

  open import Syntax.Grades.Example.Traces.LowerLift.LeftSided Op _≟ₒ_ cost
    using () renaming (_≾_ to _≾ˡᵒʷ_; _≾?_ to _≾ˡᵒʷ?_)

  order : Grade._≾_ upper-lift-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  failsˡᵒʷ : {P Q : NeTraces} {p : False (P ≾ˡᵒʷ? Q)} → ¬ (P ≾ˡᵒʷ Q)
  failsˡᵒʷ {p = p} = toWitnessFalse p

  holdsˡᵒʷ : {P Q : NeTraces} {p : True (P ≾ˡᵒʷ? Q)} → P ≾ˡᵒʷ Q
  holdsˡᵒʷ {p = p} = toWitness p

  ----------------------------------------------------------------------
  -- On singletons it is the plain floor, as `LowerLift.LeftSided` is:
  -- doing more discharges the demand, doing less does not

  logged-on-the-way : ⟅ logged-uplink ⟆ ≾ ⟅ uplink ⟆
  logged-on-the-way = holds

  did-a-poll-demanded-the-uplink : ¬ (⟅ poll ⟆ ≾ ⟅ uplink ⟆)
  did-a-poll-demanded-the-uplink = fails

  idling-is-no-read : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idling-is-no-read = fails

  ----------------------------------------------------------------------
  -- Where the two columns disagree: a box offering alternatives.
  -- Here the demand is discharged by covering *one* of them, and the
  -- uplink covers the read; the lower lift asks for every alternative
  -- to be covered, and nothing the uplink does is twenty ticks of idling

  one-alternative-suffices : ⟅ uplink ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
  one-alternative-suffices = holds

  lower-lift-wants-both : ¬ (⟅ uplink ⟆ ≾ˡᵒʷ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  lower-lift-wants-both = failsˡᵒʷ

  -- and symmetrically, an elapsed grade offering alternatives must have
  -- every one of them discharge the demand, where the lower lift is
  -- content that one does: a run that might only have polled does not
  -- open a box demanding the uplink

  might-only-have-polled : ¬ (⟅ poll ∣ uplink ⟆ ≾ ⟅ uplink ⟆)
  might-only-have-polled = fails

  lower-lift-accepts-it : ⟅ poll ∣ uplink ⟆ ≾ˡᵒʷ ⟅ uplink ⟆
  lower-lift-accepts-it = holdsˡᵒʷ

  ----------------------------------------------------------------------
  -- The unit demands nothing, so it is the greatest grade

  everything-opens-the-unit : ⟅ uplink ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆
  everything-opens-the-unit = holds {⟅ uplink ⟆} {⟅ ⟨ 0 ⟩ ⟆}

------------------------------------------------------------------------
-- A cap on what may have happened
--
-- `UpperLift.RightSided`, `traces P ≽ˢ traces Q`. Every allowance the
-- cap lists must be realised by something already elapsed.

module RightSided where

  open import Syntax.Grades.Example.Traces.UpperLift.RightSided Op _≟ₒ_ cost
    using (upper-lift-right-sided; _≾_; _≾?_) public

  open import Syntax.Grades.Example.Traces.LowerLift.RightSided Op _≟ₒ_ cost
    using () renaming (_≾_ to _≾ˡᵒʷ_; _≾?_ to _≾ˡᵒʷ?_)

  order : Grade._≾_ upper-lift-right-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  holdsˡᵒʷ : {P Q : NeTraces} {p : True (P ≾ˡᵒʷ? Q)} → P ≾ˡᵒʷ Q
  holdsˡᵒʷ {p = p} = toWitness p

  ----------------------------------------------------------------------
  -- On singletons it is the plain cap

  within-a-larger-cap : ⟅ uplink ⟆ ≾ ⟅ logged-uplink ⟆
  within-a-larger-cap = holds

  over-the-cap : ¬ (⟅ chatty-uplink ⟆ ≾ ⟅ uplink ⟆)
  over-the-cap = fails

  ----------------------------------------------------------------------
  -- Where the two columns disagree: a cap listing an allowance nothing
  -- elapsed realises. The lower lift only needs the run to fit inside
  -- *some* allowance; this one asks each allowance to be justified.

  unrealised-allowance : ¬ (⟅ uplink ⟆ ≾ ⟅ uplink ∣ ⟨ 100 ⟩ ⟆)
  unrealised-allowance = fails

  lower-lift-accepts-it : ⟅ uplink ⟆ ≾ˡᵒʷ ⟅ uplink ∣ ⟨ 100 ⟩ ⟆
  lower-lift-accepts-it = holdsˡᵒʷ

------------------------------------------------------------------------
-- Both bounds at once
--
-- `UpperLift.TwoSided`. A pair of the two above, compared endpoint by
-- endpoint and therefore in opposite argument orders.

module TwoSided where

  open import Syntax.Grades.Example.Traces.UpperLift.TwoSided Op _≟ₒ_ cost
    using (UpperInterval; [_,_,_]; lo; hi; upper-lift-two-sided;
           _≾ᵘⁱ_; _≾ᵘⁱ?_; _·ᵘⁱ_; uᵘⁱ) public

  open import Syntax.Grades.Traces.Sets Op using (traces)

  order : Grade._≾_ upper-lift-two-sided ≡ _≾ᵘⁱ_
  order = refl

  holds : (i j : UpperInterval) {p : True (i ≾ᵘⁱ? j)} → i ≾ᵘⁱ j
  holds i j {p} = toWitness p

  fails : (i j : UpperInterval) {p : False (i ≾ᵘⁱ? j)} → ¬ (i ≾ᵘⁱ j)
  fails i j {p} = toWitnessFalse p

  -- exactly one run, required and permitted

  exactly : Trace → UpperInterval
  exactly t = [ ⟅ t ⟆ , ⟅ t ⟆ , ≽ˢ-refl {traces ⟅ t ⟆} ]

  -- at least a reading, at most a full uplink

  sensed : UpperInterval
  sensed =
    [ ⟅ ⌈ read ⌉ ⟆ , ⟅ uplink ⟆
    , toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≽ˢ? traces ⟅ uplink ⟆} tt
    ]

  -- at least a tick, at most the logged uplink: wider at both ends

  loose : UpperInterval
  loose =
    [ ⟅ ⟨ 1 ⟩ ⟆ , ⟅ logged-uplink ⟆
    , toWitness {a? = traces ⟅ ⟨ 1 ⟩ ⟆ ≽ˢ? traces ⟅ logged-uplink ⟆} tt
    ]

  -- within both bounds

  the-uplink : exactly uplink ≾ᵘⁱ sensed
  the-uplink = holds (exactly uplink) sensed

  -- under the floor, and over the cap

  only-idled : ¬ (exactly idle ≾ᵘⁱ sensed)
  only-idled = fails (exactly idle) sensed

  transmitted-twice : ¬ (exactly chatty-uplink ≾ᵘⁱ sensed)
  transmitted-twice = fails (exactly chatty-uplink) sensed

  -- widening the interval weakens it, each endpoint outwards

  wider : sensed ≾ᵘⁱ loose
  wider = holds sensed loose

  narrower : ¬ (loose ≾ᵘⁱ sensed)
  narrower = fails loose sensed
