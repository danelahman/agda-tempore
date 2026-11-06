------------------------------------------------------------------------
-- Worked instances of the banked trace upper bounds, at the          --
-- allowance order.                                                   --
--                                                                    --
-- A grade lists bounds, and a computation is graded by it when every --
-- run it may have stays within one of them. The operations of a      --
-- bound are permissions, which the run may perform, and its delays   --
-- are a budget, which the run spends on idling and on operations the --
-- bound does not list, at their running time.                        --
--                                                                    --
-- Thus `⌈ read ⌉ ∙ ⟨ 6 ⟩` reads "take a reading, then spend up to    --
-- six ticks on anything": a duty-cycle budget, which specifies what  --
-- must be possible and bounds the rest by time.                      --
--                                                                    --
-- The budget is local: what a bound offers between two listed        --
-- operations pays only for what the run does between the same two. A --
-- bound thus specifies when its slack is available as well as its    --
-- amount.                                                            --
--                                                                    --
-- The set is read disjunctively: a longer list is a weaker grade.    --
-- The members are reduced to the antichain of the most permissive of --
-- them, and mutually permitting grades are equal.                    --
--                                                                    --
-- A bound charges an operation `costʰⁱ` (read 1, write 3, send 6),   --
-- the time a schedule must budget for. The runs below then take      --
--                                                                    --
--   ⌈ read ⌉                                  1 tick                 --
--   ⌈ read ⌉ ∙ ⟨ 4 ⟩                          5 ticks                --
--   ⌈ read ⌉ ∙ ⌈ write ⌉                      4 ticks                --
--   ⌈ read ⌉ ∙ ⌈ send ⌉                       7 ticks                --
--   ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉            8 ticks                --
--   ⌈ write ⌉ ∙ ⌈ read ⌉                      4 ticks                --
--                                                                    --
-- Every run is written out in full in every claim, and every claim   --
-- is established by the decision procedure of the grade.             --
------------------------------------------------------------------------

open import Grades.Durations.Nat using (ℕᵀ)
open import Data.Nat.Properties using (<⇒≢)

module Grades.Examples.Worked.Traces.Banked.UpperBound where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)

open import Util.Equality

open import Data.List.Base using ([]; _∷_)
open import Data.Unit using (tt)

open import Grades.Examples.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costʰⁱ; costʰⁱ-pos;
         read; write; send; Trace; ⌈_⌉; ⟨_⟩; _∙_; ε)

open import Grades.Examples.Traces.Banked.UpperBound
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
  using (upper-bound; upper-boundʰ; Bounds; within_; unbounded; _·ᵇ_; _≾_; _≾?_;
         ≾-antisym; ≾-⊥; Antichain; acSet)
  public

order : Grade._≾_ upper-bound ≡ _≾_
order = refl

------------------------------------------------------------------------
-- Writing down finite sets of bounds
--
-- `⟅ t ∣ u ⟆` is the grade whose members are `t` and `u`. The members
-- may be given in any order and are normalised into the canonical
-- antichain: naming a bound twice, or naming one that another member
-- already permits, names the same grade as leaving it out.

⟅_⟆ : Trace → Antichain
⟅ t ⟆ = acSet (t ∷ []) tt

⟅_∣_⟆ : Trace → Trace → Antichain
⟅ t ∣ u ⟆ = acSet (t ∷ u ∷ []) tt

⟅_∣_∣_⟆ : Trace → Trace → Trace → Antichain
⟅ t ∣ u ∣ v ⟆ = acSet (t ∷ u ∷ v ∷ []) tt

holds : {P Q : Bounds} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : Bounds} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

-- the grades taken explicitly, for the claims where they are not
-- determined by the goal alone

holdsᵉ : (P Q : Bounds) {p : True (P ≾? Q)} → P ≾ Q
holdsᵉ P Q {p} = toWitness p

failsᵉ : (P Q : Bounds) {p : False (P ≾? Q)} → ¬ (P ≾ Q)
failsᵉ P Q {p} = toWitnessFalse p

------------------------------------------------------------------------
-- What a bound permits
--
-- The reading is named, so it is permitted outright; everything after
-- it comes out of the six ticks.

reading-alone : within ⟅ ⌈ read ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
reading-alone = holds

storing-it : within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
storing-it = holds

transmitting-it :
  within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
transmitting-it = holds

-- a transmission spends the whole budget, so nothing else fits after it

transmitting-then-reading :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
transmitting-then-reading = fails

-- idling draws on the same budget as working

idling-instead : within ⟅ ⌈ read ⌉ ∙ ⟨ 4 ⟩ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
idling-instead = holds

------------------------------------------------------------------------
-- Named operations are permissions, not budget
--
-- A bound's own operation permits that operation and nothing else: it
-- does not pay for any other operation. Time pays for any operation
-- that costs no more.

a-write-needs-budget : ¬ (within ⟅ ⌈ write ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ⟆)
a-write-needs-budget = fails

three-ticks-buy-a-write : within ⟅ ⌈ write ⌉ ⟆ ≾ within ⟅ ⟨ 3 ⟩ ⟆
three-ticks-buy-a-write = holds

two-ticks-do-not : ¬ (within ⟅ ⌈ write ⌉ ⟆ ≾ within ⟅ ⟨ 2 ⟩ ⟆)
two-ticks-do-not = fails

-- and a permitted operation pays for no time: omitting it frees nothing

a-write-buys-no-time : ¬ (within ⟅ ⟨ 3 ⟩ ⟆ ≾ within ⟅ ⌈ write ⌉ ⟆)
a-write-buys-no-time = fails

------------------------------------------------------------------------
-- As an effect grade: what `coerce` may do
--
-- `coerce` takes a computation typed at `ε` to any `ε'` above it, and
-- above means "permits more". Going up, an operation turns into a delay
-- long enough to cover it, and a delay grows.

exact-to-budget :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆
exact-to-budget = holds

budgets-grow : within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
budgets-grow = holds

-- and not back: a budget permits more than the one run that prompted it

not-back-to-the-run :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
not-back-to-the-run = fails

-- offering a second bound permits more, so it too is a weakening

offering-a-second-bound :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆
offering-a-second-bound = holds

-- `return` does nothing, so every bound permits it: the unit is the
-- least grade, where for a floor it would be the greatest

pure-stays-within-anything : within ⟅ ε ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
pure-stays-within-anything =
  holdsᵉ (within ⟅ ε ⟆) (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)

-- sub-effecting a part sub-effects the whole: the product is monotone,
-- so weakening the first phase weakens the sequence

weakening-under-sequencing :
  (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ·ᵇ within ⟅ ⌈ send ⌉ ⟆)
  ≾ (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ·ᵇ within ⟅ ⌈ send ⌉ ⟆)
weakening-under-sequencing = holds

-- tightening is refused: a computation that may transmit cannot be
-- retyped at a bound that budgets four ticks

no-tightening :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 4 ⟩ ⟆)
no-tightening = fails

------------------------------------------------------------------------
-- As a resource grade: a permit that expires
--
-- `unbox`'s premise `ρ' ≾ᵣ ρ` weighs what elapsed (the product of
-- the modalities standing to the variable's right) against the grade on
-- the box, both read as upper bounds: what elapsed is still within what
-- the box allows. Overspending closes the box.

-- a permit good for a reading and six ticks' worth of work

reading-keeps-it-open :
  within ⟅ ⌈ read ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
reading-keeps-it-open = holds

storing-keeps-it-open :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
storing-keeps-it-open = holds

-- one operation too many and the permit has expired

overspending-closes-it :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
overspending-closes-it = fails

-- so does work the permit never names and has no budget for

unnamed-work-closes-it :
  ¬ (within ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ⟆)
unnamed-work-closes-it = fails

-- a permit may list alternatives, and the elapsed run need only stay
-- within one of them

either-allowance :
  within ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
either-allowance = holds

-- but the condition is universal in what elapsed, so a computation with
-- two possible runs keeps the permit open only if both stay within it

both-branches-stay-within :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
both-branches-stay-within = holds

one-branch-overspends :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
one-branch-overspends = fails

------------------------------------------------------------------------
-- Alternatives at both ends
--
-- With sets on both sides each run picks its own bound. The two runs
-- below need different ones: a pair of transmissions costs twelve
-- ticks, which no six-tick budget covers, and a reading is not
-- permitted by a bound that names only transmissions.

each-run-its-own-bound :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
each-run-its-own-bound = holds

-- and neither bound would do on its own

transmissions-need-theirs :
  ¬ (within ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
transmissions-need-theirs = fails

the-reading-needs-its-own :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ within ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
the-reading-needs-its-own = fails

-- so dropping either bound breaks the grade

dropping-the-budget :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ within ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
dropping-the-budget = fails

dropping-the-transmissions :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
dropping-the-transmissions = fails

-- a union is a join: each branch's own grade coerces into the union

union-is-a-join-left :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
union-is-a-join-left = holds

union-is-a-join-right :
  within ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
union-is-a-join-right = holds

-- a bound no run uses is harmless, the condition being existential in
-- the set

an-unused-bound :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
an-unused-bound = holds

-- a bound another listed one already permits carries no information,
-- so the members are trimmed to those that are not: the two grades
-- below are the same one

trimming :
  ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ≡ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
trimming = refl

-- the same equation read off the order, which is antisymmetric

trimming-both-ways :
  within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ≡ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆
trimming-both-ways = ≾-antisym holds holds

-- the unit is the smallest bound there is, so it is dropped from any
-- list that names another

dropping-the-empty-run :
  ⟅ ε ∣ ⌈ read ⌉ ⟆ ≡ ⟅ ⌈ read ⌉ ⟆
dropping-the-empty-run = refl

------------------------------------------------------------------------
-- Where the budget sits
--
-- Budget does not cross an operation the bound names, so a bound
-- prescribes when its spare time is available: two bounds differing
-- only in where six ticks sit each admit exactly one of two runs
-- differing only in where the store falls.

storing-in-the-window :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
storing-in-the-window = holds

storing-afterwards-does-not :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆)
storing-afterwards-does-not = fails

-- moving the three ticks the store needs to the far side of the
-- transmission exchanges which run is permitted

storing-afterwards :
  within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
storing-afterwards = holds

storing-in-the-window-does-not :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆)
storing-in-the-window-does-not = fails

-- so a computation that may do either needs a grade listing both, and
-- then each run stays within the bound that budgets where it spends

either-placement :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉
         ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
either-placement = holds

-- Placement binds only while the budget is tight. Enlarge the window to
-- nine ticks and the run that stores afterwards is permitted again,
-- its store unmoved: nine ticks pay for the transmission
-- (six) and the store after it (three), so the `⌈ send ⌉` of the bound
-- is unmatched and no listed operation separates the budget. Eight
-- ticks pay for only one of the two.

nine-ticks-buy-both-operations :
  within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 9 ⟩ ∙ ⌈ send ⌉ ⟆
nine-ticks-buy-both-operations = holds

eight-do-not :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 8 ⟩ ∙ ⌈ send ⌉ ⟆)
eight-do-not = fails

------------------------------------------------------------------------
-- The greatest grade
--
-- No finite list of bounds permits every run, so the greatest grade is
-- `unbounded`: it permits any run at all, however long, and no list of
-- bounds permits what it does. An unbounded computation leaves what
-- follows it unbounded too, `unbounded` being absorbing.

everything-weakens-to-the-top :
  within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ≾ unbounded
everything-weakens-to-the-top =
  holdsᵉ (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆) unbounded

the-top-weakens-to-no-list :
  ¬ (unbounded ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)
the-top-weakens-to-no-list = failsᵉ unbounded (within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆)

the-top-absorbs :
  (unbounded ·ᵇ within ⟅ ⌈ read ⌉ ⟆) ≡ unbounded
the-top-absorbs = refl
