------------------------------------------------------------------------
-- Worked instances of the subset grade of lower bounds.               --
--                                                                     --
-- A grade lists runs, and each of them is one the computation can      --
-- exhibit: `P ⊆ X`. The set is read *conjunctively* -- every member is --
-- a separate demand -- so a longer list demands more, dropping members --
-- weakens, and `{ ε }` demands only that stopping be possible. That is --
-- still a demand, so `{ ε }` is above exactly the lists that carry the --
-- empty run and no written-out list is above them all; `no-demand`,    --
-- which demands nothing at all, is.                                    --
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

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (left-sided; Demands; demanding_; no-demand; _·ᵈ_; _≾_; _≾?_) public

order : Grade._≾_ left-sided ≡ _≾_
order = refl

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
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ demanding ⟅ ⌈ read ⌉ ⟆
forget-a-branch = holds

no-new-demand :
  ¬ (demanding ⟅ ⌈ read ⌉ ⟆ ≾ demanding ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
no-new-demand = fails

-- `{ ε }` demands only that stopping be possible, so every list that
-- carries the empty run weakens to it -- and no other list does

anything-reachable-weakens-to-stopping :
  demanding ⟅ ε ∣ ⌈ read ⌉ ⟆ ≾ demanding ⟅ ε ⟆
anything-reachable-weakens-to-stopping =
  holdsᵉ (demanding ⟅ ε ∣ ⌈ read ⌉ ⟆) (demanding ⟅ ε ⟆)

but-stopping-must-be-reachable :
  ¬ (demanding ⟅ ⌈ read ⌉ ⟆ ≾ demanding ⟅ ε ⟆)
but-stopping-must-be-reachable =
  failsᵉ (demanding ⟅ ⌈ read ⌉ ⟆) (demanding ⟅ ε ⟆)

------------------------------------------------------------------------
-- The greatest grade
--
-- `no-demand` demands nothing, so even `{ ε }` weakens to it, and it
-- weakens to no written-out list -- every list demands some run.
-- Demanding nothing survives sequencing, `no-demand` being absorbing.

everything-weakens-to-the-top :
  demanding ⟅ ε ⟆ ≾ no-demand
everything-weakens-to-the-top = holdsᵉ (demanding ⟅ ε ⟆) no-demand

the-top-weakens-to-nothing-else :
  ¬ (no-demand ≾ demanding ⟅ ε ⟆)
the-top-weakens-to-nothing-else = failsᵉ no-demand (demanding ⟅ ε ⟆)

the-top-absorbs :
  (no-demand ·ᵈ demanding ⟅ ⌈ read ⌉ ⟆) ≡ no-demand
the-top-absorbs = refl

------------------------------------------------------------------------
-- Nothing is approximated here either
--
-- A demand for a store is met by a store and by nothing else -- not by
-- three ticks, and not the other way round. The two grades are simply
-- incomparable, where `Traces.Timed.LeftSided`'s coverage order relates
-- them.

a-store-is-not-three-ticks :
  ¬ (demanding ⟅ ⌈ write ⌉ ⟆ ≾ demanding ⟅ ⟨ 3 ⟩ ⟆)
a-store-is-not-three-ticks = fails

nor-three-ticks-a-store :
  ¬ (demanding ⟅ ⟨ 3 ⟩ ⟆ ≾ demanding ⟅ ⌈ write ⌉ ⟆)
nor-three-ticks-a-store = fails

------------------------------------------------------------------------
-- Unions are meets
--
-- A grade demanding two distinct runs is inhabited only by a branching
-- computation, whose grade is the union of what its branches offer.
-- That union lies *below* each branch's own grade, so a branching rule
-- for this endpoint has to take the union rather than coerce both
-- branches to one grade.

union-is-a-meet-belowˡ :
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ≾ demanding ⟅ ⌈ read ⌉ ⟆
union-is-a-meet-belowˡ = holds

union-is-a-meet-belowʳ :
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ≾ demanding ⟅ ⌈ write ⌉ ⟆
union-is-a-meet-belowʳ = holds

branches-have-no-common-weakening :
  ¬ (demanding ⟅ ⌈ read ⌉ ⟆ ≾ demanding ⟅ ⌈ write ⌉ ⟆)
branches-have-no-common-weakening = fails

------------------------------------------------------------------------
-- Sequencing
--
-- The language product pairs every demanded run with every demanded
-- continuation, so sequencing a two-branch computation with a
-- transmission demands both completed paths.

sequencing-pairs-the-demands :
  (demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ·ᵈ demanding ⟅ ⌈ send ⌉ ⟆)
  ≾ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
sequencing-pairs-the-demands = holds

sequencing-demands-no-mixture :
  ¬ ((demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ·ᵈ demanding ⟅ ⌈ send ⌉ ⟆)
     ≾ demanding ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
sequencing-demands-no-mixture = fails

------------------------------------------------------------------------
-- As a resource grade
--
-- A box carries a grade `ρ` and `unbox` asks `ρ' ≾ᵣ ρ` of the grade
-- `ρ'` of what has elapsed. Here `ρ` is a list of runs the box needs to
-- have remained reachable, so the box opens exactly when everything it
-- demands is among what elapsed still offers.

the-box-demands : Demands
the-box-demands = demanding ⟅ ⌈ read ⌉ ⟆

offering-more-opens-the-box :
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ the-box-demands
offering-more-opens-the-box = holds

offering-something-else-does-not :
  ¬ (demanding ⟅ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ ≾ the-box-demands)
offering-something-else-does-not = fails

-- a box demanding two runs needs both of them still offered, so a
-- computation that has shrunk to one branch no longer opens it

a-two-run-box : Demands
a-two-run-box = demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆

both-still-offered :
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ ≾ a-two-run-box
both-still-offered = holds

shrunk-to-one-branch :
  ¬ (demanding ⟅ ⌈ read ⌉ ⟆ ≾ a-two-run-box)
shrunk-to-one-branch = fails
