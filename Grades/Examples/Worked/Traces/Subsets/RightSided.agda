------------------------------------------------------------------------
-- Worked instances of the subset grade of upper bounds.              --
--                                                                    --
-- A grade lists runs, and every run of the computation is one of     --
-- them: `X ⊆ Q`. The comparison between a run and a listed trace is  --
-- equality, in contrast with `Worked.Traces.Timed.RightSided`, where --
-- a listed delay is a budget that pays for unlisted operations.      --
--                                                                    --
-- The set is read disjunctively: a longer list permits more, the     --
-- union of two grades is their join, and `{ ε }` lies below every    --
-- list containing the empty run.                                     --
--                                                                    --
-- Every run is written out in full in every claim, and every claim   --
-- is established by the decision procedure of the grade.             --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.Subsets.RightSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Worked.Operations

open import Grades.Examples.Traces.Subsets.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (right-sided; Permits; permitting_; any-run; _·ᵖ_; _≾_; _≾?_) public

order : Grade._≾_ right-sided ≡ _≾_
order = refl

holds : {P Q : Permits} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : Permits} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

-- `permitting ⟅ ε ⟆` leaves too little for the implicit arguments to
-- be found, so the endpoints are given explicitly where it appears

holdsᵉ : (P Q : Permits) {p : True (P ≾? Q)} → P ≾ Q
holdsᵉ P Q {p} = toWitness p

failsᵉ : (P Q : Permits) {p : False (P ≾? Q)} → ¬ (P ≾ Q)
failsᵉ P Q {p} = toWitnessFalse p

------------------------------------------------------------------------
-- Permitting more
--
-- As an effect grade: `coerce` moves along `≾`, adding runs to the
-- list of runs a computation may have, never allowing one that is not
-- listed.

permit-a-second-run :
  permitting ⟅ ⌈ read ⌉ ⟆ ≾ permitting ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
permit-a-second-run = holds

no-dropping-runs :
  ¬ (permitting ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ permitting ⟅ ⌈ read ⌉ ⟆)
no-dropping-runs = fails

-- `return` has grade `{ ε }`, which weakens only to grades that list
-- the empty run: `{ ε }` is not the least grade

pure-fits-where-stopping-is-listed :
  permitting ⟅ ε ⟆ ≾ permitting ⟅ ε ∣ ⌈ read ⌉ ⟆
pure-fits-where-stopping-is-listed =
  holdsᵉ (permitting ⟅ ε ⟆) (permitting ⟅ ε ∣ ⌈ read ⌉ ⟆)

pure-does-not-fit-elsewhere :
  ¬ (permitting ⟅ ε ⟆ ≾ permitting ⟅ ⌈ read ⌉ ⟆)
pure-does-not-fit-elsewhere =
  failsᵉ (permitting ⟅ ε ⟆) (permitting ⟅ ⌈ read ⌉ ⟆)

------------------------------------------------------------------------
-- The greatest grade
--
-- `any-run` permits any run at all, so every written-out list weakens
-- to it, and it weakens to none of them, a finite list leaving some
-- run unpermitted. Permitting everything survives sequencing,
-- `any-run` being absorbing.

everything-weakens-to-the-top :
  permitting ⟅ ⌈ read ⌉ ⟆ ≾ any-run
everything-weakens-to-the-top = holdsᵉ (permitting ⟅ ⌈ read ⌉ ⟆) any-run

the-top-weakens-to-nothing-else :
  ¬ (any-run ≾ permitting ⟅ ⌈ read ⌉ ⟆)
the-top-weakens-to-nothing-else = failsᵉ any-run (permitting ⟅ ⌈ read ⌉ ⟆)

the-top-absorbs :
  (any-run ·ᵖ permitting ⟅ ⌈ read ⌉ ⟆) ≡ any-run
the-top-absorbs = refl

------------------------------------------------------------------------
-- Nothing is approximated
--
-- The comparison is equality, so a listed delay pays for no operation
-- and a listed operation permits nothing but itself. Both comparisons
-- below hold in `Traces.Timed.RightSided`, where the allowance order
-- lets time pay for operations.

a-store-is-not-three-ticks :
  ¬ (permitting ⟅ ⌈ write ⌉ ⟆ ≾ permitting ⟅ ⟨ 3 ⟩ ⟆)
a-store-is-not-three-ticks = fails

a-budget-buys-nothing :
  ¬ (permitting ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ permitting ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
a-budget-buys-nothing = fails

-- a grade lists the run itself

listing-it-works :
  permitting ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ permitting ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
listing-it-works = holds

------------------------------------------------------------------------
-- Unions are joins
--
-- Each branch's runs are permitted by the union, and any grade
-- permitting both permits it, so a branching construct would grade
-- its result by listing what each branch may do.

union-is-a-join-inˡ :
  permitting ⟅ ⌈ read ⌉ ⟆ ≾ permitting ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆
union-is-a-join-inˡ = holds

union-is-a-join-inʳ :
  permitting ⟅ ⌈ send ⌉ ⟆ ≾ permitting ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆
union-is-a-join-inʳ = holds

union-is-a-join-least :
  permitting ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆
  ≾ permitting ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆
union-is-a-join-least = holds

------------------------------------------------------------------------
-- Sequencing
--
-- The monoid is the language product, so sequencing a branching
-- computation with a further step pairs every listed run with every
-- listed continuation.

sequencing-pairs-the-runs :
  (permitting ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ·ᵖ permitting ⟅ ⌈ send ⌉ ⟆)
  ≾ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
sequencing-pairs-the-runs = holds

sequencing-adds-nothing-else :
  ¬ ((permitting ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ·ᵖ permitting ⟅ ⌈ send ⌉ ⟆)
     ≾ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
sequencing-adds-nothing-else = fails

------------------------------------------------------------------------
-- As a resource grade
--
-- A box carries a grade `ρ`, and `unbox` asks the grade `ρ'` of what
-- has elapsed to satisfy `ρ' ≾ᵣ ρ`. So the box names the runs it
-- tolerates, and opens exactly when every run that may have happened
-- is one of them.

the-box-tolerates : Permits
the-box-tolerates = permitting ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆

a-listed-run-opens-the-box :
  permitting ⟅ ⌈ read ⌉ ⟆ ≾ the-box-tolerates
a-listed-run-opens-the-box = holds

an-unlisted-run-does-not :
  ¬ (permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ≾ the-box-tolerates)
an-unlisted-run-does-not = fails

-- and a branching computation opens it only if every branch is
-- listed, the elapsed grade being read disjunctively too

both-branches-listed :
  permitting ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ the-box-tolerates
both-branches-listed = holds

one-branch-not-listed :
  ¬ (permitting ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ ≾ the-box-tolerates)
one-branch-not-listed = fails
