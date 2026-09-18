------------------------------------------------------------------------
-- Worked instances of the subset grade of lower bounds.               --
--                                                                     --
-- A grade lists runs, and each of them is one the computation can      --
-- exhibit: `P ⊆ X`. The set is read *conjunctively* -- every member is --
-- a separate demand -- so a longer list demands more, dropping members --
-- weakens, and `{ ε }` demands only that stopping be possible. That is --
-- still a demand, so `{ ε }` is above exactly the lists that carry the --
-- empty run and no written-out list is above them all; the adjoined    --
-- `⊤ᵍ`, which demands nothing at all, is.                              --
--                                                                     --
-- That is the reverse of every other endpoint in this development, and --
-- it is forced: with equality as the comparison, the disjunctive       --
-- reading "whatever happened, it was one of the listed traces" is      --
-- `X ⊆ P`, which is the cap's own condition. A subset floor has to be  --
-- conjunctive or it is not a floor.                                    --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure.                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Subsets.LeftSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

import Syntax.Grades.Example.Worked.Operations as Ops

open import Syntax.Grades.Example.Worked.Operations
  hiding (⟅_⟆; ⟅_∣_⟆; ⟅_∣_∣_⟆; _·_)

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (left-sided; Demands; only_; ⊤ᵍ; _≾_; _≾?_)
  renaming (_·ᵈ_ to _·_) public

order : Grade._≾_ left-sided ≡ _≾_
order = refl

-- a written-out list of demanded runs is a grade under `only`; `⊤ᵍ`
-- demands no run at all

⟅_⟆ : Trace → Demands
⟅ t ⟆ = only Ops.⟅ t ⟆

⟅_∣_⟆ : Trace → Trace → Demands
⟅ t ∣ u ⟆ = only Ops.⟅ t ∣ u ⟆

⟅_∣_∣_⟆ : Trace → Trace → Trace → Demands
⟅ t ∣ u ∣ v ⟆ = only Ops.⟅ t ∣ u ∣ v ⟆

holds : {P Q : Demands} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : Demands} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

holdsᵉ : (P Q : Demands) {p : True (P ≾? Q)} → P ≾ Q
holdsᵉ P Q {p} = toWitness p

failsᵉ : (P Q : Demands) {p : False (P ≾? Q)} → ¬ (P ≾ Q)
failsᵉ P Q {p} = toWitnessFalse p

------------------------------------------------------------------------
-- Demanding less
--
-- Read as an *effect* grade: `coerce` moves along `≾`, and here that
-- means forgetting that some run is reachable. It can never mean
-- claiming a further one is.

forget-a-branch :
  ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
forget-a-branch = holds

no-new-demand :
  ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
no-new-demand = fails

-- `{ ε }` demands only that stopping be possible, so every list that
-- carries the empty run weakens to it -- and no other list does

anything-reachable-weakens-to-stopping :
  ⟅ ε ∣ ⌈ read ⌉ ⟆ ≾ ⟅ ε ⟆
anything-reachable-weakens-to-stopping = holdsᵉ ⟅ ε ∣ ⌈ read ⌉ ⟆ ⟅ ε ⟆

but-stopping-must-be-reachable :
  ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ε ⟆)
but-stopping-must-be-reachable = failsᵉ ⟅ ⌈ read ⌉ ⟆ ⟅ ε ⟆

------------------------------------------------------------------------
-- The adjoined point
--
-- `⊤ᵍ` demands nothing, so even `{ ε }` weakens to it, and it weakens to
-- no written-out list -- every list demands some run. Demanding nothing
-- survives sequencing, `⊤ᵍ` being absorbing.

everything-weakens-to-the-top :
  ⟅ ε ⟆ ≾ ⊤ᵍ
everything-weakens-to-the-top = holdsᵉ ⟅ ε ⟆ ⊤ᵍ

the-top-weakens-to-nothing-else :
  ¬ (⊤ᵍ ≾ ⟅ ε ⟆)
the-top-weakens-to-nothing-else = failsᵉ ⊤ᵍ ⟅ ε ⟆

the-top-absorbs :
  (⊤ᵍ · ⟅ ⌈ read ⌉ ⟆) ≡ ⊤ᵍ
the-top-absorbs = refl

------------------------------------------------------------------------
-- Nothing is approximated here either
--
-- A demand for a store is met by a store and by nothing else -- not by
-- three ticks, and not the other way round. The two grades are simply
-- incomparable, where `Traces.Timed.LeftSided`'s coverage order relates
-- them.

a-store-is-not-three-ticks :
  ¬ (⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 3 ⟩ ⟆)
a-store-is-not-three-ticks = fails

nor-three-ticks-a-store :
  ¬ (⟅ ⟨ 3 ⟩ ⟆ ≾ ⟅ ⌈ write ⌉ ⟆)
nor-three-ticks-a-store = fails

------------------------------------------------------------------------
-- Unions are meets, which is what a non-singleton grade costs
--
-- A computation has one run at a time, so a grade demanding two
-- distinct runs is inhabited only by a branching one, and the grade it
-- gets is the union of what its branches offer. The union lies *below*
-- each branch's own grade, so it cannot be reached by weakening the two
-- branches to a common grade -- the common weakening would be their
-- intersection, which may be empty and is not a grade at all.
--
-- A branching rule for this endpoint therefore has to take the union of
-- its branches' grades rather than coerce both to one grade.

union-is-a-meet-belowˡ :
  ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
union-is-a-meet-belowˡ = holds

union-is-a-meet-belowʳ :
  ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ write ⌉ ⟆
union-is-a-meet-belowʳ = holds

branches-have-no-common-weakening :
  ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ write ⌉ ⟆)
branches-have-no-common-weakening = fails

------------------------------------------------------------------------
-- Sequencing
--
-- The language product pairs every demanded run with every demanded
-- continuation, so sequencing a two-branch computation with a
-- transmission demands both completed paths.

sequencing-pairs-the-demands :
  (⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ · ⟅ ⌈ send ⌉ ⟆) ≾ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
sequencing-pairs-the-demands = holds

sequencing-demands-no-mixture :
  ¬ ((⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ · ⟅ ⌈ send ⌉ ⟆) ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
sequencing-demands-no-mixture = fails

------------------------------------------------------------------------
-- As a resource grade
--
-- A box carries a grade `ρ` and `unbox` asks `ρ' ≾ᵣ ρ` of the grade
-- `ρ'` of what has elapsed. Here `ρ` is a list of runs the box needs to
-- have remained reachable, so the box opens exactly when everything it
-- demands is among what elapsed still offers.

the-box-demands : Demands
the-box-demands = ⟅ ⌈ read ⌉ ⟆

offering-more-opens-the-box :
  ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ the-box-demands
offering-more-opens-the-box = holds

offering-something-else-does-not :
  ¬ (⟅ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ ≾ the-box-demands)
offering-something-else-does-not = fails

-- a box demanding two runs needs both of them still offered, so a
-- computation that has narrowed to one branch no longer opens it

a-two-run-box : Demands
a-two-run-box = ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆

both-still-offered :
  ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ ≾ a-two-run-box
both-still-offered = holds

narrowed-to-one-branch :
  ¬ (⟅ ⌈ read ⌉ ⟆ ≾ a-two-run-box)
narrowed-to-one-branch = fails
