------------------------------------------------------------------------
-- Worked instances of the convex column over the time-strict          --
-- sub-trace order.                                                    --
--                                                                     --
-- `Grades.Example.Traces.SubtraceTimed.Convex`: each grade of          --
-- `SubtraceTimed.LowerLift` strengthened by the Smyth partner of its   --
-- comparison, so that as well as every trace on one side being matched --
-- on the other, every trace on the other side is matched back.        --
--                                                                     --
-- Between singleton grades the extra half is vacuous, and what remains --
-- is the window discipline the order itself imposes -- so the          --
-- singleton claims here are `SubtraceTimed.LowerLift`'s. The columns   --
-- part company as soon as either side offers alternatives, and there   --
-- both axes are in play at once: an alternative that logs outside the  --
-- window is one this order cannot match back.                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.SubtraceTimed.Convex where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.SubtraceTimedLift Op _≟ₒ_ cost
  using (≼ˢ-refl; ≽ˢ-refl)

------------------------------------------------------------------------
-- A floor, convexly compared
--
-- `SubtraceTimed.Convex.LeftSided`. The time-strict floor plus the
-- demand that every listed alternative be achievable by a run already
-- on offer -- achievable, now, at the times the alternative names.

module LeftSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.LeftSided
    Op _≟ₒ_ cost using (convex-left-sided; _≾_; _≾?_) public

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵒʷ_; _≾?_ to _≾ˡᵒʷ?_)

  open import Syntax.Grades.Example.Traces.Subtrace.Convex.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵉⁿ_; _≾?_ to _≾ˡᵉⁿ?_)

  order : Grade._≾_ convex-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  holdsˡᵒʷ : {P Q : NeTraces} {p : True (P ≾ˡᵒʷ? Q)} → P ≾ˡᵒʷ Q
  holdsˡᵒʷ {p = p} = toWitness p

  holdsˡᵉⁿ : {P Q : NeTraces} {p : True (P ≾ˡᵉⁿ? Q)} → P ≾ˡᵉⁿ Q
  holdsˡᵉⁿ {p = p} = toWitness p

  ----------------------------------------------------------------------
  -- Between singleton grades the two halves coincide, so all that is
  -- left is the window discipline

  -- an operation interleaved in the middle is still tolerated: what is
  -- restricted is when a run may spend time, not what it may do on the
  -- way (`SubtraceTimed.LowerLift.LeftSided.logged-on-the-way`)

  logged-on-the-way : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-on-the-way = holds

  logged-in-the-window : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                         ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-in-the-window = holds

  logged-too-early : ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
                       ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  logged-too-early = fails

  logged-too-early-passes-leniently : ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
                                      ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-too-early-passes-leniently = holdsˡᵉⁿ

  only-polled : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  only-polled = fails

  ----------------------------------------------------------------------
  -- Both axes at once
  --
  -- A run that might have logged in the window and might have logged
  -- too early. The Hoare half is content -- the demand is covered by
  -- the first alternative -- but the Smyth half asks the second to be
  -- matched back, and under this order it is not. Over the lenient
  -- order it is, so there the convex column accepts the pair.

  might-have-logged-too-early :
    ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  might-have-logged-too-early = fails

  the-hoare-half-alone-accepts-it :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵒʷ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  the-hoare-half-alone-accepts-it = holdsˡᵒʷ

  leniently-convex-accepts-it :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  leniently-convex-accepts-it = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- The convex strengthening on its own, with the order held fixed: an
  -- elapsed grade that might have done nothing at all still covers the
  -- demanded read on one of its alternatives, which is all the plain
  -- floor asks. The Smyth half asks every alternative to cover a listed
  -- demand, and the instantaneous one covers none.

  might-have-done-nothing : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 0 ⟩ ⟆
                              ≾ ⟅ ⌈ read ⌉ ⟆)
  might-have-done-nothing = fails

  the-plain-floor-allows-it : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 0 ⟩ ⟆
                              ≾ˡᵒʷ ⟅ ⌈ read ⌉ ⟆
  the-plain-floor-allows-it = holdsˡᵒʷ

------------------------------------------------------------------------
-- A cap, convexly compared
--
-- `SubtraceTimed.Convex.RightSided`, the mirror image: the same
-- conjunction with the two sets in the order they are written.

module RightSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.RightSided
    Op _≟ₒ_ cost using (convex-right-sided; _≾_; _≾?_) public

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵒʷ_; _≾?_ to _≾ˡᵒʷ?_)

  open import Syntax.Grades.Example.Traces.Subtrace.Convex.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵉⁿ_; _≾?_ to _≾ˡᵉⁿ?_)

  order : Grade._≾_ convex-right-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  holdsˡᵒʷ : {P Q : NeTraces} {p : True (P ≾ˡᵒʷ? Q)} → P ≾ˡᵒʷ Q
  holdsˡᵒʷ {p = p} = toWitness p

  holdsˡᵉⁿ : {P Q : NeTraces} {p : True (P ≾ˡᵉⁿ? Q)} → P ≾ˡᵉⁿ Q
  holdsˡᵉⁿ {p = p} = toWitness p

  ----------------------------------------------------------------------
  -- On singletons, the window discipline again

  the-window-permits-it : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                          ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  the-window-permits-it = holds

  logging-early-does-not : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                             ≾ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  logging-early-does-not = fails

  logging-early-does-leniently : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                                 ≾ˡᵉⁿ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  logging-early-does-leniently = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- Both axes at once, on the cap side
  --
  -- A cap offering both placements of the write. The Hoare half is
  -- content -- the run fits inside the first -- but the Smyth half asks
  -- the second to be realised, and under this order the uplink does not
  -- realise it.

  an-allowance-that-cannot-be-taken :
    ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
      ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  an-allowance-that-cannot-be-taken = fails

  the-plain-cap-allows-it :
    ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵒʷ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  the-plain-cap-allows-it = holdsˡᵒʷ

  leniently-convex-allows-it :
    ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  leniently-convex-allows-it = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- The unit permits only the instantaneous run

  nothing-fits-in-the-unit : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆)
  nothing-fits-in-the-unit = fails

------------------------------------------------------------------------
-- Both bounds at once
--
-- `SubtraceTimed.Convex.TwoSided`. A pair of the two above, compared
-- endpoint by endpoint and therefore in opposite directions, with the
-- consistency field the convex comparison of the endpoints.

module TwoSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.TwoSided
    Op _≟ₒ_ cost using (ConvexInterval; [_,_,_]; lo; hi; convex-two-sided;
                        _≾ᶜⁱ_; _≾ᶜⁱ?_; _·ᶜⁱ_; uᶜⁱ) public

  open import Syntax.Grades.Traces.Sets Op using (traces)
  open import Syntax.Grades.Traces.SubtraceTimedLift Op _≟ₒ_ cost
    using (_≼ˢ_; _≼ˢ?_; _≽ˢ?_)

  order : Grade._≾_ convex-two-sided ≡ _≾ᶜⁱ_
  order = refl

  holds : (i j : ConvexInterval) {p : True (i ≾ᶜⁱ? j)} → i ≾ᶜⁱ j
  holds i j {p} = toWitness p

  fails : (i j : ConvexInterval) {p : False (i ≾ᶜⁱ? j)} → ¬ (i ≾ᶜⁱ j)
  fails i j {p} = toWitnessFalse p

  -- exactly one run, required and permitted

  exactly : Trace → ConvexInterval
  exactly t =
    [ ⟅ t ⟆ , ⟅ t ⟆ , (≼ˢ-refl {traces ⟅ t ⟆} , ≽ˢ-refl {traces ⟅ t ⟆}) ]

  -- at least a read, at most the uplink schedule

  sensed : ConvexInterval
  sensed =
    [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ( toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
      , toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≽ˢ? traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt )
    ]

  -- at least the uplink schedule, at most the run that logs between the
  -- read and the send: consistent only because the write falls inside
  -- the window the floor names

  logged-in-the-window : ConvexInterval
  logged-in-the-window =
    [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
    , ( toWitness {a? = traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                      ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆} tt
      , toWitness {a? = traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                      ≽ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆} tt )
    ]

  ----------------------------------------------------------------------
  -- The same pair with the write moved before the read is not an
  -- interval at all for this order: neither half of the consistency
  -- field can be filled, which is the two-sided reading of
  -- `LeftSided.logged-too-early`

  ¬logged-too-early : ¬ (traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                         ≼ˢ traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  ¬logged-too-early =
    toWitnessFalse {a? = traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                       ≼ˢ? traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆} tt

  ----------------------------------------------------------------------
  -- Widening at both ends weakens the grade

  a-read-sits-inside : exactly ⌈ read ⌉ ≾ᶜⁱ sensed
  a-read-sits-inside = holds (exactly ⌈ read ⌉) sensed

  raised-into-the-window : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                           ≾ᶜⁱ logged-in-the-window
  raised-into-the-window =
    holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) logged-in-the-window

  the-uplink-does-not-sit-in-a-read : ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                                          ≾ᶜⁱ exactly ⌈ read ⌉)
  the-uplink-does-not-sit-in-a-read =
    fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) (exactly ⌈ read ⌉)

  ----------------------------------------------------------------------
  -- The unit requires and permits nothing but the instantaneous run

  nothing-but-the-unit-is-below-it : ¬ (exactly ⌈ read ⌉ ≾ᶜⁱ uᶜⁱ)
  nothing-but-the-unit-is-below-it = fails (exactly ⌈ read ⌉) uᶜⁱ
