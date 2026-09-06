------------------------------------------------------------------------
-- Worked instances of the convex column.                              --
--                                                                     --
-- `Grades.Example.Traces.Subtrace.Convex`: each grade of `LowerLift`  --
-- strengthened by the Smyth partner of its comparison, so that as well --
-- as every trace on one side being matched on the other, every trace   --
-- on the other side is matched back.                                   --
--                                                                     --
-- Between singleton grades the extra half is vacuous and the column    --
-- agrees with `LowerLift`; the examples below are chosen so that they --
-- part company as soon as either side offers alternatives.            --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Subtrace.Convex where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost
  using (≼ˢ-refl; ≽ˢ-refl)

------------------------------------------------------------------------
-- A floor, convexly compared
--
-- `Convex.LeftSided`. `LowerLift.LeftSided`'s floor plus the demand that
-- every listed alternative be achievable by a run already on offer.

module LeftSided where

  open import Syntax.Grades.Example.Traces.Subtrace.Convex.LeftSided Op _≟ₒ_ cost
    using (convex-left-sided; _≾_; _≾?_) public

  order : Grade._≾_ convex-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  -- between singleton grades the two halves coincide, so the order
  -- agrees with the plain floor: doing more opens the box, doing less
  -- does not, and idling never buys an operation

  logged-on-the-way : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-on-the-way = holds

  only-polled : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  only-polled = fails

  idling-is-no-read : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idling-is-no-read = fails

  -- they part company once the box offers alternatives: nothing the
  -- uplink does amounts to twenty ticks, so that alternative is not
  -- achievable and the convex order rejects it

  unreachable-alternative : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                              ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  unreachable-alternative = fails

  reachable-alternatives : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                           ≾ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  reachable-alternatives = holds

------------------------------------------------------------------------
-- A cap, convexly compared
--
-- `Convex.RightSided`, the mirror image: `LowerLift.RightSided`'s cap
-- plus the demand that every listed allowance be realised by one
-- already present.

module RightSided where

  open import Syntax.Grades.Example.Traces.Subtrace.Convex.RightSided Op _≟ₒ_ cost
    using (convex-right-sided; _≾_; _≾?_) public

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.RightSided Op _≟ₒ_ cost
    using () renaming (_≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_)

  order : Grade._≾_ convex-right-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  holdsʰⁱ : {P Q : NeTraces} {p : True (P ≾ʰⁱ? Q)} → P ≾ʰⁱ Q
  holdsʰⁱ {p = p} = toWitness p

  -- between singletons, as before, the plain cap: staying within a
  -- larger allowance is weaker

  within-a-larger-cap : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                        ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  within-a-larger-cap = holds

  over-the-cap : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
                   ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  over-the-cap = fails

  -- and they part company once the cap offers alternatives: a cap that
  -- permits a hundred ticks of idling as well is weaker for the plain
  -- order, but the convex one asks that idling too be realised by
  -- something already permitted, and the uplink is not idling

  unrealised-allowance : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                           ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 100 ⟩ ⟆)
  unrealised-allowance = fails

  plain-cap-accepts-it : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                         ≾ʰⁱ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 100 ⟩ ⟆
  plain-cap-accepts-it = holdsʰⁱ

------------------------------------------------------------------------
-- Both bounds at once
--
-- `Convex.TwoSided`. A pair of the two above, compared endpoint by
-- endpoint and therefore in opposite directions, with the consistency
-- field the convex comparison of the endpoints.

module TwoSided where

  open import Syntax.Grades.Example.Traces.Subtrace.Convex.TwoSided Op _≟ₒ_ cost
    using (ConvexInterval; [_,_,_]; lo; hi; convex-two-sided;
           _≾ᶜⁱ_; _≾ᶜⁱ?_; _·ᶜⁱ_; uᶜⁱ) public

  open import Syntax.Grades.Traces.Sets Op using (traces)
  open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost
    using (_≼ˢ?_; _≽ˢ?_)

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

  -- at least a reading, at most a full uplink

  sensed : ConvexInterval
  sensed =
    [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ( toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
      , toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≽ˢ? traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt )
    ]

  -- at least a tick, at most the logged uplink: wider at both ends

  loose : ConvexInterval
  loose =
    [ ⟅ ⟨ 1 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ( toWitness {a? = traces ⟅ ⟨ 1 ⟩ ⟆ ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
      , toWitness {a? = traces ⟅ ⟨ 1 ⟩ ⟆ ≽ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt )
    ]

  -- an interval listing alternatives at both endpoints. The consistency
  -- field is convex here, so it asks more than `LowerLift.TwoSided`'s:
  -- as well as each floor run fitting inside some cap run, each cap run
  -- must have some floor run inside it.

  branching : ConvexInterval
  branching =
    [ ⟅ ⌈ read ⌉ ∣ ⟨ 1 ⟩ ⟆
    , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ( toWitness
          {a? = traces ⟅ ⌈ read ⌉ ∣ ⟨ 1 ⟩ ⟆
             ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉
                        ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
      , toWitness
          {a? = traces ⟅ ⌈ read ⌉ ∣ ⟨ 1 ⟩ ⟆
             ≽ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉
                        ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt )
    ]

  ----------------------------------------------------------------------
  -- What the convex column refuses that the lower lift allows.
  --
  -- Widening a cap by an allowance nothing already permitted realises
  -- is a weakening for `LowerLift.TwoSided` and not for this one: the
  -- Smyth half of the cap comparison asks each new allowance to be
  -- justified by an old one, and the uplink is not a store-and-stop.

  uplink-not-into-branching :
    ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉) ≾ᶜⁱ branching)
  uplink-not-into-branching =
    fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) branching

  -- a branching interval is still below itself, so the refusal above is
  -- about the pair and not about branching intervals as such

  branching-reflexive : branching ≾ᶜⁱ branching
  branching-reflexive = holds branching branching

  -- within both bounds

  the-uplink : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉) ≾ᶜⁱ sensed
  the-uplink = holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) sensed

  -- under the floor, and over the cap

  only-idled : ¬ (exactly ⟨ 2 ⟩ ≾ᶜⁱ sensed)
  only-idled = fails (exactly ⟨ 2 ⟩) sensed

  transmitted-twice : ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉)
                        ≾ᶜⁱ sensed)
  transmitted-twice = fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉)) sensed

  -- widening the interval weakens it, each endpoint outwards

  wider : sensed ≾ᶜⁱ loose
  wider = holds sensed loose

  narrower : ¬ (loose ≾ᶜⁱ sensed)
  narrower = fails loose sensed
