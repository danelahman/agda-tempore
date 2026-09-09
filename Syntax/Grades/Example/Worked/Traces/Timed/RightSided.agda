------------------------------------------------------------------------
-- Worked instances of the trace grade of upper bounds, at the         --
-- allowance order.                                                    --
--                                                                     --
-- A grade lists bounds, and a computation is graded by it when every   --
-- run it may have stays within one of them. A bound's operations are   --
-- permissions -- the run may perform them -- and its delays are a      --
-- budget, which the run spends on idling and on operations the bound   --
-- does not name, at their execution time.                             --
--                                                                     --
-- So `⌈ read ⌉ ∙ ⟨ 6 ⟩` reads "take a reading, then spend up to six    --
-- ticks however you like", which is the shape of a duty-cycle budget:  --
-- it says what must be possible and caps the rest by time rather than  --
-- by naming it.                                                       --
--                                                                     --
-- Budget is *local*: what a bound offers between two operations it     --
-- names pays only for what the run does between those same two. A      --
-- bound therefore says when its slack is available, and not merely how --
-- much of it there is -- the last section below turns on that alone.   --
--                                                                     --
-- Under `cost` -- read 1, write 3, send 6 -- the runs below take       --
--                                                                     --
--   ⌈ read ⌉                                  1 tick                  --
--   ⌈ read ⌉ ∙ ⟨ 4 ⟩                          5 ticks                 --
--   ⌈ read ⌉ ∙ ⌈ write ⌉                      4 ticks                 --
--   ⌈ read ⌉ ∙ ⌈ send ⌉                       7 ticks                 --
--   ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉            8 ticks                 --
--   ⌈ write ⌉ ∙ ⌈ read ⌉                      4 ticks                 --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure, so a table     --
-- asserted the wrong way round does not typecheck.                     --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Timed.RightSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ cost cost-pos
  using (right-sided; _≾_; _≾?_) public

order : Grade._≾_ right-sided ≡ _≾_
order = refl

holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

-- the sets taken explicitly, for the claims where they are not
-- determined by the goal alone

holdsᵉ : (P Q : NeTraces) {p : True (P ≾? Q)} → P ≾ Q
holdsᵉ P Q {p} = toWitness p

------------------------------------------------------------------------
-- What a bound permits
--
-- The reading is named, so it is permitted outright; everything after
-- it comes out of the six ticks.

reading-alone : ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
reading-alone = holds

storing-it : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
storing-it = holds

transmitting-it : ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
transmitting-it = holds

-- a transmission spends the whole budget, so nothing else fits after it

transmitting-then-reading :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
transmitting-then-reading = fails

-- idling draws on the same budget as working

idling-instead : ⟅ ⌈ read ⌉ ∙ ⟨ 4 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
idling-instead = holds

------------------------------------------------------------------------
-- Named operations are permissions, not budget
--
-- A bound's own operation permits that operation and nothing else: it
-- is not worth its execution time to anything the run does instead.
-- Time, by contrast, buys any work that costs no more.

a-write-needs-budget : ¬ (⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
a-write-needs-budget = fails

three-ticks-buy-a-write : ⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 3 ⟩ ⟆
three-ticks-buy-a-write = holds

two-ticks-do-not : ¬ (⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 2 ⟩ ⟆)
two-ticks-do-not = fails

-- and a permitted operation buys no time: skipping it frees nothing

a-write-buys-no-time : ¬ (⟅ ⟨ 3 ⟩ ⟆ ≾ ⟅ ⌈ write ⌉ ⟆)
a-write-buys-no-time = fails

------------------------------------------------------------------------
-- As an effect grade: what `coerce` may do
--
-- `coerce` takes a computation typed at `ε` to any `ε'` above it, and
-- above means "permits more". Going up, an operation turns into a delay
-- long enough to cover it, and a delay grows.

exact-to-budget :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆
exact-to-budget = holds

budgets-grow : ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
budgets-grow = holds

-- and not back: a budget permits more than the one run that prompted it

not-back-to-the-run :
  ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
not-back-to-the-run = fails

-- offering a second bound permits more, so it too is a weakening

offering-a-second-bound :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆
offering-a-second-bound = holds

-- `return` does nothing, so every bound permits it -- the unit is the
-- least grade, where for a floor it would be the greatest

pure-stays-within-anything : ⟅ ε ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
pure-stays-within-anything = holdsᵉ ⟅ ε ⟆ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆

-- sub-effecting a part sub-effects the whole: the product is monotone,
-- so weakening the first phase weakens the sequence

weakening-under-sequencing :
  (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ · ⟅ ⌈ send ⌉ ⟆)
  ≾ (⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ · ⟅ ⌈ send ⌉ ⟆)
weakening-under-sequencing = holds

-- tightening is refused: a computation that may transmit cannot be
-- retyped at a bound that budgets four ticks

no-tightening :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 4 ⟩ ⟆)
no-tightening = fails

------------------------------------------------------------------------
-- As a resource grade: a permit that expires
--
-- `unbox`'s premise `ρ' ≾ᵣ ρ` has `ρ'` the product of the locks
-- standing to the variable's right -- what elapsed -- and `ρ` the grade
-- on the box. With both read as upper bounds it says: what elapsed is
-- still within what the box allows. A box is then a permit valid while
-- the computation stays inside its allowance, and overspending closes
-- it.

-- a permit good for a reading and six ticks' worth of work

reading-keeps-it-open :
  ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
reading-keeps-it-open = holds

storing-keeps-it-open :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
storing-keeps-it-open = holds

-- one operation too many and the permit has expired

overspending-closes-it :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
overspending-closes-it = fails

-- so does work the permit never names and has no budget for

unnamed-work-closes-it :
  ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
unnamed-work-closes-it = fails

-- a permit may list alternatives, and the elapsed run need only stay
-- within one of them

either-allowance :
  ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
either-allowance = holds

-- but the condition is universal in what elapsed, so a computation with
-- two possible runs keeps the permit open only if both stay within it

both-branches-stay-within :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 4 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
both-branches-stay-within = holds

one-branch-overspends :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
one-branch-overspends = fails

------------------------------------------------------------------------
-- Alternatives at both ends
--
-- With sets on both sides each run picks its own bound. The two runs
-- below need different ones: a pair of transmissions costs twelve
-- ticks, which no six-tick budget covers, and a reading is not
-- permitted by a bound that names only transmissions.

each-run-its-own-bound :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
each-run-its-own-bound = holds

-- and neither bound would do on its own

transmissions-need-theirs :
  ¬ (⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
transmissions-need-theirs = fails

the-reading-needs-its-own :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
the-reading-needs-its-own = fails

-- so dropping either bound breaks the grade

dropping-the-budget :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
dropping-the-budget = fails

dropping-the-transmissions :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
dropping-the-transmissions = fails

-- a union is a join: each branch's own grade coerces into the union

union-is-a-join-left :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
union-is-a-join-left = holds

union-is-a-join-right :
  ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
union-is-a-join-right = holds

-- a bound no run uses is harmless, the condition being existential in
-- the set

an-unused-bound :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
an-unused-bound = holds

-- and a bound already covered by another may be dropped again: a set
-- trims to those that are not

trimming :
  ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
trimming = holds

untrimming :
  ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆
untrimming = holds

------------------------------------------------------------------------
-- Where the budget sits
--
-- Budget does not cross an operation the bound names, so a bound
-- prescribes when its spare time is available. Two bounds differing
-- only in where six ticks sit, against two runs differing only in where
-- the store falls -- all four traces performing a read, a store and a
-- transmission, and all taking ten ticks -- and each bound admits
-- exactly one of the runs.

storing-in-the-window :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
storing-in-the-window = holds

storing-afterwards-does-not :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆)
storing-afterwards-does-not = fails

-- moving the three ticks the store needs to the far side of the
-- transmission exchanges which run is permitted

storing-afterwards :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
storing-afterwards = holds

storing-in-the-window-does-not :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆)
storing-in-the-window-does-not = fails

-- so a computation that may do either needs a grade listing both, and
-- then each run stays within the bound that budgets where it spends

either-placement :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
either-placement = holds

-- Placement binds only while the budget is tight. Widen the window to
-- nine ticks and the run that stores afterwards is permitted again --
-- but not because its store moved: nine buys the transmission outright
-- (six) and the store after it (three), so the bound's own `⌈ send ⌉`
-- goes unmatched and there is no match left for budget to fail to
-- cross. Eight ticks buy only one of the two.

nine-ticks-buy-both-operations :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 9 ⟩ ∙ ⌈ send ⌉ ⟆
nine-ticks-buy-both-operations = holds

eight-do-not :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 8 ⟩ ∙ ⌈ send ⌉ ⟆)
eight-do-not = fails
