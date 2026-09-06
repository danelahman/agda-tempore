------------------------------------------------------------------------
-- Worked instances of the two trace-set grades that are not intervals. --
--                                                                     --
-- `Inclusion` compares sets by membership alone, never consulting the  --
-- sub-trace preorder, so it bounds a run in neither direction.         --
-- `Convex` is the Egli-Milner lift: the floor of                       --
-- `Worked.TraceIntervals.LeftSided` plus a demand that every listed    --
-- alternative be achievable. Despite the name it is not a two-sided    --
-- interval and never caps a run from above.                            --
--                                                                     --
-- As there, every claim is stated with the grade's own order `_≾_`     --
-- between two sets of traces written out in full, in the form `unbox`  --
-- reads it -- `ρ' ≾ ρ`, elapsed on the left, the box's grade on the    --
-- right -- and closed by `holds` or `fails`, which run the order's     --
-- decision procedure.                                                  --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.TraceSets where

open import Data.Product using (_×_; _,_; proj₂)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

------------------------------------------------------------------------
-- Sets of traces ordered by inclusion
--
-- `Grades.Example.TraceSet.Inclusion`. A box is opened only by having
-- done literally one of the runs listed, so nothing that appeals to the
-- sub-trace preorder is available -- and the operations need no
-- execution times at all.

module Inclusion where

  open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
    using (traces-by-inclusion; _≾_; _≾?_) public

  order : Grade._≾_ traces-by-inclusion ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  -- doing exactly what is listed opens the box

  the-listed-run : ⟅ uplink ⟆ ≾ ⟅ uplink ⟆
  the-listed-run = holds

  one-of-those-listed : ⟅ uplink ⟆ ≾ ⟅ poll ∣ uplink ⟆
  one-of-those-listed = holds

  -- doing more does not, "more" not being on the list

  logged-on-the-way : ¬ (⟅ logged-uplink ⟆ ≾ ⟅ uplink ⟆)
  logged-on-the-way = fails

  -- nor does doing less

  only-polled : ¬ (⟅ poll ⟆ ≾ ⟅ uplink ⟆)
  only-polled = fails

  -- nor does spending the time an operation would have taken

  a-tick-is-no-read : ¬ (⟅ ⟨ 1 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  a-tick-is-no-read = fails

  a-read-is-no-tick : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 1 ⟩ ⟆)
  a-read-is-no-tick = fails

------------------------------------------------------------------------
-- Sets of traces ordered by the convex (Egli-Milner) lift
--
-- `Grades.Example.TraceSet.Convex`. The left-sided order, plus the
-- requirement that every listed alternative be achievable by a run the
-- elapsed grade already offers.

module Convex where

  open import Syntax.Grades.Example.TraceSet.Convex Op _≟ₒ_ cost
    using (traces-convex; _≾_; _≾?_) public

  order : Grade._≾_ traces-convex ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  -- between singleton grades the two halves coincide, so the order
  -- agrees with the left-sided one: doing more opens the box, doing
  -- less does not, and idling never buys an operation

  logged-on-the-way : ⟅ logged-uplink ⟆ ≾ ⟅ uplink ⟆
  logged-on-the-way = holds

  only-polled : ¬ (⟅ poll ⟆ ≾ ⟅ uplink ⟆)
  only-polled = fails

  idling-is-no-read : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idling-is-no-read = fails

  -- they part company once the box offers alternatives. The left-sided
  -- order is content for the uplink to take the first; the convex order
  -- also asks that the second be achievable, and nothing the uplink
  -- does amounts to twenty ticks.

  unreachable-alternative : ¬ (⟅ uplink ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  unreachable-alternative = fails

  reachable-alternatives : ⟅ logged-uplink ⟆ ≾ ⟅ ⌈ read ⌉ ∣ uplink ⟆
  reachable-alternatives = holds

------------------------------------------------------------------------
-- How these two sit against the left-sided grade
--
-- Both are contained in it -- inclusion because a listed run covers
-- itself, the convex order because it is that order plus a second
-- condition. Both containments are strict, and inclusion and the convex
-- order are incomparable.

module Comparison where

  open import Syntax.Grades.Example.Worked.TraceIntervals
    using (module LeftSided)

  open Inclusion using () renaming (_≾_ to _≾ⁱ_)
  open Convex    using () renaming (_≾_ to _≾ᶜ_)
  open LeftSided using () renaming (_≾_ to _≾ˡᵒ_)

  convex⇒left-sided : {P Q : NeTraces} → P ≾ᶜ Q → P ≾ˡᵒ Q
  convex⇒left-sided = proj₂

  -- the convex order accepts what inclusion rejects: doing more than
  -- was listed

  convex-not-inclusion :
      (⟅ logged-uplink ⟆ ≾ᶜ ⟅ uplink ⟆)
    × ¬ (⟅ logged-uplink ⟆ ≾ⁱ ⟅ uplink ⟆)
  convex-not-inclusion = Convex.logged-on-the-way , Inclusion.logged-on-the-way

  -- and inclusion accepts what the convex order rejects: a listed
  -- alternative that nothing elapsed can achieve

  inclusion-not-convex :
      (⟅ ⟨ 20 ⟩ ⟆ ≾ⁱ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
    × ¬ (⟅ ⟨ 20 ⟩ ⟆ ≾ᶜ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  inclusion-not-convex = Inclusion.holds , Convex.fails

  -- both are strictly inside the left-sided order, which accepts the
  -- unreachable alternative and the unlisted run alike

  left-sided-accepts-both :
      (⟅ uplink ⟆ ≾ˡᵒ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
    × (⟅ logged-uplink ⟆ ≾ˡᵒ ⟅ uplink ⟆)
  left-sided-accepts-both =
    LeftSided.either-way-of-opening-it , LeftSided.logged-on-the-way
