------------------------------------------------------------------------
-- Worked instances of the inclusion column.                           --
--                                                                     --
-- `Grades.Example.Traces.Inclusion`: a run matches a listed one only --
-- by *being* it, so nothing here consults the sub-trace preorder and   --
-- the operations' execution times are never read.                     --
--                                                                     --
-- The two one-sided grades are the same comparison with the sets       --
-- exchanged, so they disagree exactly where the sets differ in size:   --
-- adding an alternative weakens a cap and strengthens a floor.         --
--                                                                     --
-- As elsewhere in `Worked`, every claim is closed by `holds` or        --
-- `fails`, which run the order's own decision procedure, so a claim    --
-- asserted the wrong way round does not typecheck.                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Inclusion where

open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

------------------------------------------------------------------------
-- A cap: no run beyond those listed
--
-- `Inclusion.RightSided`, `P ⊆ Q`. Weakening permits more runs.

module RightSided where

  open import Syntax.Grades.Example.Traces.Inclusion.RightSided Op _≟ₒ_
    using (inclusion-right-sided; _≾_; _≾?_) public

  order : Grade._≾_ inclusion-right-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  -- doing exactly what is permitted stays within the cap

  the-listed-run : ⟅ uplink ⟆ ≾ ⟅ uplink ⟆
  the-listed-run = holds

  -- and a cap that permits more is weaker

  one-of-those-permitted : ⟅ uplink ⟆ ≾ ⟅ poll ∣ uplink ⟆
  one-of-those-permitted = holds

  -- doing more than permitted does not, "more" not being on the list

  logged-on-the-way : ¬ (⟅ logged-uplink ⟆ ≾ ⟅ uplink ⟆)
  logged-on-the-way = fails

  -- nor does doing less: inclusion bounds in neither direction of `_≼_`

  only-polled : ¬ (⟅ poll ⟆ ≾ ⟅ uplink ⟆)
  only-polled = fails

  -- nor does spending the time an operation would have taken

  a-tick-is-no-read : ¬ (⟅ ⟨ 1 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  a-tick-is-no-read = fails

  a-read-is-no-tick : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 1 ⟩ ⟆)
  a-read-is-no-tick = fails

------------------------------------------------------------------------
-- A floor: every listed run must be among those had
--
-- `Inclusion.LeftSided`, `Q ⊆ P`. Weakening requires fewer runs, so the
-- inclusion runs against the way it is written.

module LeftSided where

  open import Syntax.Grades.Example.Traces.Inclusion.LeftSided Op _≟ₒ_
    using (inclusion-left-sided; _≾_; _≾?_) public

  order : Grade._≾_ inclusion-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  -- requiring exactly what is on offer

  the-required-run : ⟅ uplink ⟆ ≾ ⟅ uplink ⟆
  the-required-run = holds

  -- dropping a requirement weakens the floor -- the direction in which
  -- this grade differs from the cap above

  one-requirement-fewer : ⟅ poll ∣ uplink ⟆ ≾ ⟅ uplink ⟆
  one-requirement-fewer = holds

  -- and adding one strengthens it, so the same pair the other way round
  -- fails: nothing offers a poll

  one-requirement-more : ¬ (⟅ uplink ⟆ ≾ ⟅ poll ∣ uplink ⟆)
  one-requirement-more = fails

  -- the two one-sided grades genuinely part company on that pair

  cap-and-floor-disagree :
      (RightSided._≾_ ⟅ uplink ⟆ ⟅ poll ∣ uplink ⟆)
    → ¬ (⟅ uplink ⟆ ≾ ⟅ poll ∣ uplink ⟆)
  cap-and-floor-disagree _ = one-requirement-more

------------------------------------------------------------------------
-- Both bounds at once
--
-- `Inclusion.TwoSided`. A pair of the two above, compared endpoint by
-- endpoint and therefore in opposite directions: the floor may lose a
-- requirement and the cap may gain a permission.
--
-- The consistency field asks `lo ⊆ hi` -- what is required must be
-- permitted -- which is the analogue of `min ≤ max`. It is what rules
-- out pairing a floor with a cap that does not list it; the sub-trace
-- column admits such pairs, because there `lo` need only be *covered*
-- by `hi` rather than listed in it.

module TwoSided where

  open import Syntax.Grades.Example.Traces.Inclusion.TwoSided Op _≟ₒ_
    using (InclusionInterval; [_,_,_]; lo; hi; inclusion-two-sided;
           _≾ⁱⁱ_; _≾ⁱⁱ?_; _·ⁱⁱ_; uⁱⁱ) public

  open import Syntax.Grades.Traces.Sets Op using (traces)
  open WithDecEq _≟ₒ_ using (_⊑?_; ⊑-refl)

  order : Grade._≾_ inclusion-two-sided ≡ _≾ⁱⁱ_
  order = refl

  holds : (i j : InclusionInterval) {p : True (i ≾ⁱⁱ? j)} → i ≾ⁱⁱ j
  holds i j {p} = toWitness p

  fails : (i j : InclusionInterval) {p : False (i ≾ⁱⁱ? j)} → ¬ (i ≾ⁱⁱ j)
  fails i j {p} = toWitnessFalse p

  -- exactly one run, required and permitted

  exactly : Trace → InclusionInterval
  exactly t = [ ⟅ t ⟆ , ⟅ t ⟆ , ⊑-refl {traces ⟅ t ⟆} ]

  -- a poll and an uplink both required, and nothing else permitted

  both-runs : InclusionInterval
  both-runs =
    [ ⟅ poll ∣ uplink ⟆ , ⟅ poll ∣ uplink ⟆
    , ⊑-refl {traces ⟅ poll ∣ uplink ⟆}
    ]

  -- only the uplink required, and the logged run permitted as well

  looser : InclusionInterval
  looser =
    [ ⟅ uplink ⟆ , ⟅ poll ∣ uplink ∣ logged ⟆
    , toWitness
        {a? = traces ⟅ uplink ⟆ ⊑? traces ⟅ poll ∣ uplink ∣ logged ⟆} tt
    ]

  -- the two inclusions run in opposite directions: the floor lost the
  -- poll, the cap gained the logged run

  wider : both-runs ≾ⁱⁱ looser
  wider = holds both-runs looser

  narrower : ¬ (looser ≾ⁱⁱ both-runs)
  narrower = fails looser both-runs

  -- an interval is below itself, and a singleton below one whose cap
  -- lists it among others

  reflexive : exactly uplink ≾ⁱⁱ exactly uplink
  reflexive = holds (exactly uplink) (exactly uplink)

  -- but not below one that requires a run it does not offer

  missing-the-poll : ¬ (exactly uplink ≾ⁱⁱ both-runs)
  missing-the-poll = fails (exactly uplink) both-runs
