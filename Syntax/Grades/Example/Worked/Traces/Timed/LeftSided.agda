------------------------------------------------------------------------
-- Worked instances of the trace grade of guarantees, at the coverage  --
-- order.                                                              --
--                                                                     --
-- A grade lists traces, and whatever the computation does, at least    --
-- one of them has been covered: every operation it names occurred, in  --
-- order, and every delay it names was spent where it is placed. So     --
-- `⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉` reads "took a reading, let it settle   --
-- two ticks, then transmitted", and settling time counts only if it    --
-- falls between the two.                                              --
--                                                                     --
-- The set is read *disjunctively*: a longer list is a weaker grade,    --
-- since there are more ways to have discharged it. That is what makes  --
-- the union of two grades their join, and it is the reading a          --
-- branching construct needs.                                          --
--                                                                     --
-- Under `cost` -- read 1, write 3, send 6 -- the runs below take       --
--                                                                     --
--   ⌈ read ⌉                                       1 tick             --
--   ⌈ write ⌉                                      3 ticks            --
--   ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉               10 ticks            --
--   ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉               10 ticks            --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉                    9 ticks            --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure.                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Timed.LeftSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.Timed.LeftSided Op _≟ₒ_ cost
  using (left-sided; _≾_; _≾?_) public

order : Grade._≾_ left-sided ≡ _≾_
order = refl

holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

holdsᵉ : (P Q : NeTraces) {p : True (P ≾? Q)} → P ≾ Q
holdsᵉ P Q {p} = toWitness p

failsᵉ : (P Q : NeTraces) {p : False (P ≾? Q)} → ¬ (P ≾ Q)
failsᵉ P Q {p} = toWitnessFalse p

------------------------------------------------------------------------
-- Guaranteeing less
--
-- A guarantee weakens by asking for less of the same run, and by
-- offering further ways of being discharged. It never weakens by
-- asking for more.

drop-to-the-reading :
  ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
drop-to-the-reading = holds

offer-a-second-way :
  ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆
offer-a-second-way = holds

no-stronger-guarantee :
  ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
no-stronger-guarantee = fails

-- `return` guarantees nothing, and nothing is all it can be weakened to

pure-guarantees-nothing : ¬ (⟅ ε ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
pure-guarantees-nothing = failsᵉ ⟅ ε ⟆ ⟅ ⌈ read ⌉ ⟆

everything-guarantees-the-empty-trace : ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ε ⟆
everything-guarantees-the-empty-trace = holdsᵉ ⟅ ⌈ read ⌉ ⟆ ⟅ ε ⟆

------------------------------------------------------------------------
-- An operation guarantees the time it takes
--
-- The direction that holds is operation to time: a store covers a
-- three-tick guarantee, at its execution time. Time never covers an
-- operation, which is what a guarantee needs and what the allowance
-- order deliberately does not have.

a-store-guarantees-three-ticks : ⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 3 ⟩ ⟆
a-store-guarantees-three-ticks = holds

three-ticks-guarantee-no-store : ¬ (⟅ ⟨ 3 ⟩ ⟆ ≾ ⟅ ⌈ write ⌉ ⟆)
three-ticks-guarantee-no-store = fails

-- and not more time than it takes

a-store-guarantees-no-fourth-tick : ¬ (⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 4 ⟩ ⟆)
a-store-guarantees-no-fourth-tick = fails

------------------------------------------------------------------------
-- A named delay counts only where it is named
--
-- The guarantee asks for two ticks *between* the reading and the
-- transmission. A run that stores in that window covers it; one that
-- stores before the reading does not, though it performs the same
-- operations and takes the same ten ticks.

storing-in-the-window :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
storing-in-the-window = holds

storing-before-the-reading :
  ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
storing-before-the-reading = fails

-- both runs do guarantee the weaker "read then transmit", which names
-- no delay at all

both-guarantee-the-bare-pair :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
both-guarantee-the-bare-pair = holds

------------------------------------------------------------------------
-- As an effect grade: what `coerce` may do
--
-- Every claim above is a coercion. Two more that matter: sub-effecting
-- passes through sequencing, and a computation with two possible runs
-- is graded by listing what each guarantees.

weakening-under-sequencing :
  (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ · ⟅ ⌈ send ⌉ ⟆)
  ≾ (⟅ ⌈ read ⌉ ⟆ · ⟅ ⌈ send ⌉ ⟆)
weakening-under-sequencing = holds

union-is-a-join-left :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆
union-is-a-join-left = holds

union-is-a-join-right :
  ⟅ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆
union-is-a-join-right = holds

-- and the union cannot be trimmed to a branch that the other run does
-- not cover

no-dropping-a-branch :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
no-dropping-a-branch = fails

------------------------------------------------------------------------
-- As a resource grade: what opens a box
--
-- `unbox`'s premise `ρ' ≾ᵣ ρ` has `ρ'` the product of the locks
-- standing to the variable's right -- what elapsed -- and `ρ` the grade
-- on the box. Here it reads: whatever elapsed covers one of the demands
-- the box lists. A box listing more demands is easier to open, and a
-- box demanding an operation is not opened by waiting.

the-uplink-opens-a-reading-box :
  ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
the-uplink-opens-a-reading-box = holds

waiting-does-not :
  ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
waiting-does-not = fails

-- a box with two ways of becoming ready is opened by elapsed grades
-- that satisfy different ones

either-demand :
  ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
either-demand = holds

-- but the condition is universal in what elapsed, so a computation with
-- two possible runs opens the box only if both cover a listed demand

both-branches-open-it :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
both-branches-open-it = holds

one-branch-does-not :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
one-branch-does-not = fails
