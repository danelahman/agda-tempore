------------------------------------------------------------------------
-- Worked instances of the inclusion column.                           --
--                                                                     --
-- `Grades.Example.Traces.Inclusion`: a run matches a listed one only   --
-- by *being* it, so nothing here consults the sub-trace preorder and   --
-- the operations' execution times are never read. That makes this the  --
-- column where the two one-sided grades differ purely by which way the --
-- inclusion points, and where sets with several members are the only   --
-- thing that can tell them apart at all.                              --
--                                                                     --
-- The runs are written out in full rather than through the shorthands  --
-- of `Worked.Operations`, so that each claim can be read on its own:   --
--                                                                     --
--   ⌈ read ⌉                                a poll                    --
--   ⌈ read ⌉ ∙ ⌈ write ⌉                    read, then store          --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉            read, idle, transmit      --
--                                                                     --
-- Every claim is closed by `holds` or `fails`, which run the order's   --
-- own decision procedure, so a claim asserted the wrong way round does --
-- not typecheck.                                                      --
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
-- A floor: every listed run must be among those had
--
-- `Inclusion.LeftSided`, `Q ⊆ P`. Weakening requires fewer runs, so the
-- inclusion runs against the way it is written. On singletons this is
-- indistinguishable from the cap below; the alternatives are what
-- separate them.

module LeftSided where

  open import Syntax.Grades.Example.Traces.Inclusion.LeftSided Op _≟ₒ_
    using (inclusion-left-sided; _≾_; _≾?_) public

  order : Grade._≾_ inclusion-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- Singletons: exactly as the cap behaves, which is the collapse the
  -- inclusion column is subject to at one member

  the-required-run : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                   ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  the-required-run = holds

  a-different-run : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  a-different-run = fails

  ----------------------------------------------------------------------
  -- Alternatives: for a floor, weakening *drops* requirements -- the
  -- opposite of the cap, and the only place the two columns differ

  one-requirement-fewer :
    ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
  one-requirement-fewer = holds

  cannot-add-a-requirement :
    ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  cannot-add-a-requirement = fails

  -- dropping two of three requirements is still a weakening

  three-down-to-one :
    ⟅ ⌈ read ⌉
    ∣ ⌈ read ⌉ ∙ ⌈ write ⌉
    ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  three-down-to-one = holds

  -- but a requirement that was never offered cannot appear

  a-requirement-from-nowhere :
    ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  a-requirement-from-nowhere = fails

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

  ----------------------------------------------------------------------
  -- Singletons: only doing exactly what is permitted stays within the cap

  the-listed-run : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                 ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  the-listed-run = holds

  -- doing more than permitted does not, "more" not being on the list

  stored-on-the-way : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                       ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  stored-on-the-way = fails

  -- nor does doing less: inclusion bounds in neither direction of `_≼_`

  only-polled : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  only-polled = fails

  -- nor does spending the time an operation would have taken, in either
  -- direction: a read costs one tick, and one tick is not a read

  a-tick-is-no-read : ¬ (⟅ ⟨ 1 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  a-tick-is-no-read = fails

  a-read-is-no-tick : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 1 ⟩ ⟆)
  a-read-is-no-tick = fails

  ----------------------------------------------------------------------
  -- Alternatives: for a cap, weakening *adds* permissions

  one-more-permission : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                      ≾ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  one-more-permission = holds

  -- and every listed run must be permitted, so a cap that drops one is
  -- strictly stronger

  cannot-drop-a-permission :
    ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  cannot-drop-a-permission = fails

  -- both sets may list several runs, provided every one on the left is
  -- listed on the right

  two-of-three : ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
               ≾ ⟅ ⌈ read ⌉
                 ∣ ⌈ read ⌉ ∙ ⌈ write ⌉
                 ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  two-of-three = holds

  -- one member missing is enough to break it: the store-and-send run is
  -- on neither side of the list on the right

  one-member-short :
    ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
      ≾ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
  one-member-short = fails

  -- the very same pair on which the floor above goes the other way:
  -- side by side, this is the whole difference between the two grades

  cap-adds-what-the-floor-drops :
      ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    → ¬ (LeftSided._≾_ ⟅ ⌈ read ⌉ ⟆
                       ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  cap-adds-what-the-floor-drops _ = LeftSided.cannot-add-a-requirement

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
-- columns admit such pairs, because there `lo` need only be *covered*
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

  ----------------------------------------------------------------------
  -- Writing intervals down. `exactly t` requires and permits just `t`;
  -- the others list several runs at one or both endpoints.

  exactly : Trace → InclusionInterval
  exactly t = [ ⟅ t ⟆ , ⟅ t ⟆ , ⊑-refl {traces ⟅ t ⟆} ]

  -- a poll and an uplink both required, and nothing else permitted

  both-required : InclusionInterval
  both-required =
    [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ⊑-refl {traces ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆}
    ]

  -- only the uplink still required, and the store-and-send run
  -- permitted as well: the floor lost a run and the cap gained one

  looser : InclusionInterval
  looser =
    [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ⟅ ⌈ read ⌉
      ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉
      ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
    , toWitness
        {a? = traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
           ⊑? traces ⟅ ⌈ read ⌉
                     ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉
                     ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆} tt
    ]

  -- the cap widened but the floor left alone: only one endpoint moved

  cap-only : InclusionInterval
  cap-only =
    [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ⟅ ⌈ read ⌉
      ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉
      ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
    , toWitness
        {a? = traces ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
           ⊑? traces ⟅ ⌈ read ⌉
                     ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉
                     ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆} tt
    ]

  ----------------------------------------------------------------------
  -- Both endpoints moving outwards is a weakening, and the two
  -- inclusions run in opposite directions while doing so

  wider : both-required ≾ⁱⁱ looser
  wider = holds both-required looser

  narrower : ¬ (looser ≾ⁱⁱ both-required)
  narrower = fails looser both-required

  -- moving one endpoint alone is still a weakening, in either endpoint

  cap-alone : both-required ≾ⁱⁱ cap-only
  cap-alone = holds both-required cap-only

  floor-alone : cap-only ≾ⁱⁱ looser
  floor-alone = holds cap-only looser

  ----------------------------------------------------------------------
  -- What a pair cannot do: move an endpoint the wrong way. Requiring a
  -- run the other interval does not is a strengthening, not a weakening,
  -- even though the cap is unchanged.

  floor-cannot-grow : ¬ (cap-only ≾ⁱⁱ both-required)
  floor-cannot-grow = fails cap-only both-required

  -- and a singleton interval is below one that requires a run it does
  -- not offer

  missing-the-poll : ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                       ≾ⁱⁱ both-required)
  missing-the-poll = fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) both-required

  -- reflexivity, and the singleton sitting inside the widened pair

  reflexive : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
            ≾ⁱⁱ exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
  reflexive = holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉))
                    (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉))

  singleton-into-looser : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉) ≾ⁱⁱ looser
  singleton-into-looser =
    holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) looser
