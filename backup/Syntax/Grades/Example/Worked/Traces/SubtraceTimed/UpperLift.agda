------------------------------------------------------------------------
-- Worked instances of the upper-lift column over the time-strict      --
-- sub-trace order.                                                    --
--                                                                     --
-- `Grades.Example.Traces.SubtraceTimed.UpperLift`: the time-strict     --
-- matching of `SubtraceTimed.LowerLift`, quantified over the other set --
-- of the pair.                                                        --
--                                                                     --
-- Two axes vary independently here, and the examples are chosen to     --
-- separate them. Which *order* is lifted decides whether a run may     --
-- bank time across a matched operation; which *lift* is taken decides  --
-- which set the quantifier runs over. On singleton grades the second   --
-- makes no difference and only the first is visible; as soon as either --
-- side lists alternatives both are, and the claims below are stated    --
-- against the timed lower lift and the lenient upper lift as well, so  --
-- each axis is decided rather than asserted.                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.SubtraceTimed.UpperLift where

open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.SubtraceTimedLift Op _≟ₒ_ cost
  using (≽ˢ-refl; _≽ˢ?_)

------------------------------------------------------------------------
-- A floor under what must have happened
--
-- `SubtraceTimed.UpperLift.LeftSided`, `traces Q ≽ˢ traces P`: every
-- run the grade admits must cover one of the listed demands, each
-- demanded delay paid for in its own window.

module LeftSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.LeftSided
    Op _≟ₒ_ cost using (upper-lift-left-sided; _≾_; _≾?_) public

  -- the other lift at the same order, and the same lift at the lenient
  -- order: the carrier is `NeTraces` throughout, so all three compare
  -- the same pairs of sets

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵒʷ_; _≾?_ to _≾ˡᵒʷ?_)

  open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵉⁿ_; _≾?_ to _≾ˡᵉⁿ?_)

  order : Grade._≾_ upper-lift-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  holdsˡᵒʷ : {P Q : NeTraces} {p : True (P ≾ˡᵒʷ? Q)} → P ≾ˡᵒʷ Q
  holdsˡᵒʷ {p = p} = toWitness p

  holdsˡᵉⁿ : {P Q : NeTraces} {p : True (P ≾ˡᵉⁿ? Q)} → P ≾ˡᵉⁿ Q
  holdsˡᵉⁿ {p = p} = toWitness p

  failsˡᵉⁿ : {P Q : NeTraces} {p : False (P ≾ˡᵉⁿ? Q)} → ¬ (P ≾ˡᵉⁿ Q)
  failsˡᵉⁿ {p = p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- On singletons it is the plain floor, and the window discipline is
  -- the only thing that distinguishes it from the lenient column

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

  idling-is-no-read : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idling-is-no-read = fails

  ----------------------------------------------------------------------
  -- Where the two axes cross
  --
  -- A run that might have logged in the window and might have logged
  -- too early. The upper lift asks *every* possibility to cover the
  -- demand, so the early one sinks it; the lower lift is content that
  -- one of them does; and over the lenient order the early one covers
  -- the demand too, so there the upper lift accepts it as well.

  might-have-logged-too-early :
    ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  might-have-logged-too-early = fails

  lower-lift-accepts-it :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵒʷ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  lower-lift-accepts-it = holdsˡᵒʷ

  leniently-both-cover-it :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  leniently-both-cover-it = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- The lift's own behaviour is unchanged: a box offering alternatives
  -- is opened by covering one of them

  one-alternative-suffices : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                             ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
  one-alternative-suffices = holds

  ----------------------------------------------------------------------
  -- The unit demands nothing, so it is the greatest grade

  everything-opens-the-unit : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆
  everything-opens-the-unit =
    holds {⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} {⟅ ⟨ 0 ⟩ ⟆}

------------------------------------------------------------------------
-- A cap on what may have happened
--
-- `SubtraceTimed.UpperLift.RightSided`, `traces P ≽ˢ traces Q`. Every
-- allowance the cap lists must be realised by something already
-- elapsed, and now realised at the times the allowance names.

module RightSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.RightSided
    Op _≟ₒ_ cost using (upper-lift-right-sided; _≾_; _≾?_) public

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵒʷ_; _≾?_ to _≾ˡᵒʷ?_)

  open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵉⁿ_; _≾?_ to _≾ˡᵉⁿ?_)

  order : Grade._≾_ upper-lift-right-sided ≡ _≾_
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
  -- On singletons it is the plain cap, subject to the window discipline

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
  -- Where the two axes cross, on the cap side
  --
  -- A cap offering both placements of the write. The upper lift asks
  -- every listed allowance to be realised, and the early one is not
  -- realisable by the uplink under this order; the lower lift only asks
  -- that the run fit inside one of them.

  every-allowance-must-be-realised :
    ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
      ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  every-allowance-must-be-realised = fails

  one-allowance-is-enough-for-the-lower-lift :
    ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵒʷ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  one-allowance-is-enough-for-the-lower-lift = holdsˡᵒʷ

  leniently-both-are-realised :
    ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  leniently-both-are-realised = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- The unit permits only the instantaneous run

  nothing-fits-in-the-unit : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆)
  nothing-fits-in-the-unit = fails

------------------------------------------------------------------------
-- Both at once
--
-- `SubtraceTimed.UpperLift.TwoSided`. A pair of the two above, compared
-- endpoint by endpoint and therefore in opposite argument orders.

module TwoSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.TwoSided
    Op _≟ₒ_ cost using (UpperInterval; [_,_,_]; lo; hi; upper-lift-two-sided;
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

  -- at least a read, at most the uplink schedule

  sensed : UpperInterval
  sensed =
    [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≽ˢ? traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
    ]

  -- at least the uplink schedule, at most the run that logs between the
  -- read and the send: an interval only the window discipline admits

  logged-in-the-window : UpperInterval
  logged-in-the-window =
    [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
    , toWitness {a? = traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                    ≽ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆} tt
    ]

  ----------------------------------------------------------------------
  -- Widening at both ends weakens the grade

  a-read-sits-inside : exactly ⌈ read ⌉ ≾ᵘⁱ sensed
  a-read-sits-inside = holds (exactly ⌈ read ⌉) sensed

  the-uplink-does-not : ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                            ≾ᵘⁱ exactly ⌈ read ⌉)
  the-uplink-does-not =
    fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) (exactly ⌈ read ⌉)

  raised-into-the-window : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                           ≾ᵘⁱ logged-in-the-window
  raised-into-the-window =
    holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) logged-in-the-window

  ----------------------------------------------------------------------
  -- The unit requires and permits nothing but the instantaneous run

  the-unit : uᵘⁱ ≡ [ ⟅ ⟨ 0 ⟩ ⟆ , ⟅ ⟨ 0 ⟩ ⟆ , ≽ˢ-refl {traces ⟅ ⟨ 0 ⟩ ⟆} ]
  the-unit = refl

  nothing-but-the-unit-is-below-it : ¬ (exactly ⌈ read ⌉ ≾ᵘⁱ uᵘⁱ)
  nothing-but-the-unit-is-below-it = fails (exactly ⌈ read ⌉) uᵘⁱ
