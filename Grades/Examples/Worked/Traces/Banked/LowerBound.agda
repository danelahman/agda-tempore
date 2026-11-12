------------------------------------------------------------------------
-- Worked instances of the banked trace lower bounds, at the coverage --
-- order.                                                             --
--                                                                    --
-- A grade lists traces, and in every run of the computation at least --
-- one of them is covered: every operation it lists occurred, in      --
-- order, and every delay it lists elapsed where it is placed. Thus   --
-- `⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉` reads "took a reading, let it settle --
-- for two ticks, then transmitted", and settling time counts only if --
-- it falls between the two operations.                               --
--                                                                    --
-- The set is read disjunctively: a longer list is a weaker grade,    --
-- and the union of two grades is their join. The members are reduced --
-- to the antichain of the weakest of them, and mutually weakening    --
-- grades are equal.                                                  --
--                                                                    --
-- A guarantee credits an operation with `costˡᵒ` (read 1, write 2,   --
-- send 4), the time it is certain to take. The runs below are then   --
-- guaranteed                                                         --
--                                                                    --
--   ⌈ read ⌉                                       1 tick            --
--   ⌈ write ⌉                                      2 ticks           --
--   ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉                7 ticks           --
--   ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉                7 ticks           --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉                    7 ticks           --
--                                                                    --
-- The product does not commute.                                      --
--                                                                    --
-- Every run is written out in full in every claim, and every claim   --
-- is established by the decision procedure of the grade.             --
------------------------------------------------------------------------

open import Grades.Durations.Nat using (ℕᵀ)

module Grades.Examples.Worked.Traces.Banked.LowerBound where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)

open import Util.Equality

open import Data.List.Base using ([]; _∷_)
open import Data.Unit using (tt)

open import Grades.Examples.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costˡᵒ;
         read; write; send; Trace; ⌈_⌉; ⟨_⟩; _∙_; ε)

open import Grades.Examples.Traces.Banked.LowerBound
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (lower-bound; _≾_; _≾?_; ≾-⊤; ≾-antisym; Antichain; acSet; _·_; 𝟏)
  public

order : Grade._≾_ lower-bound ≡ _≾_
order = refl

------------------------------------------------------------------------
-- Writing down finite sets of traces
--
-- `⟅ t ∣ u ⟆` is the grade whose members are `t` and `u`. The members
-- may be given in any order and are normalised into the canonical
-- antichain: naming a trace twice, or naming one that another member
-- already guarantees, names the same grade as leaving it out.

⟅_⟆ : Trace → Antichain
⟅ t ⟆ = acSet (t ∷ []) tt

⟅_∣_⟆ : Trace → Trace → Antichain
⟅ t ∣ u ⟆ = acSet (t ∷ u ∷ []) tt

⟅_∣_∣_⟆ : Trace → Trace → Trace → Antichain
⟅ t ∣ u ∣ v ⟆ = acSet (t ∷ u ∷ v ∷ []) tt

holds : {P Q : Antichain} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : Antichain} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

holdsᵉ : (P Q : Antichain) {p : True (P ≾? Q)} → P ≾ Q
holdsᵉ P Q {p} = toWitness p

failsᵉ : (P Q : Antichain) {p : False (P ≾? Q)} → ¬ (P ≾ Q)
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
-- two-tick guarantee, at its best-case running time. Time never covers
-- an operation, as a guarantee requires; under the allowance order it
-- does.

a-store-guarantees-two-ticks : ⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 2 ⟩ ⟆
a-store-guarantees-two-ticks = holds

two-ticks-guarantee-no-store : ¬ (⟅ ⟨ 2 ⟩ ⟆ ≾ ⟅ ⌈ write ⌉ ⟆)
two-ticks-guarantee-no-store = fails

-- and not more time than it is certain to take: a store may run to
-- three ticks, but only two of them are guaranteed

a-store-guarantees-no-third-tick : ¬ (⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 3 ⟩ ⟆)
a-store-guarantees-no-third-tick = fails

------------------------------------------------------------------------
-- A named delay counts only where it is named
--
-- The guarantee asks for two ticks between the reading and the
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
-- Every claim above is a coercion. Further: sub-effecting passes
-- through sequencing, and a computation with two possible runs is
-- graded by listing what each guarantees.

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
-- `unbox`'s premise `ρ' ≾ᵣ ρ` weighs what elapsed (the product of
-- the modalities standing to the variable's right) against the grade on
-- the box: whatever elapsed covers one of the demands the box lists. A
-- box listing more demands is easier to open, and waiting opens no box
-- that demands an operation.

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

------------------------------------------------------------------------
-- The greatest grade
--
-- The unit `{ ε }` already guarantees nothing, the empty run being
-- covered by every run, so every grade weakens to it and it is the
-- designated greatest one.

everything-weakens : (P : Antichain) → P ≾ 𝟏
everything-weakens = ≾-⊤

the-unit-is-greatest : Grade.⊤ lower-bound ≡ 𝟏
the-unit-is-greatest = refl

------------------------------------------------------------------------
-- Mutually-weakening grades are equal
--
-- A listed guarantee that another listed one already implies carries
-- no information: a run covering `⌈ read ⌉ ∙ ⌈ write ⌉` covers
-- `⌈ read ⌉ ` too, so the longer trace is dropped and the two grades
-- are the same one.

a-redundant-branch :
  ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≡ ⟅ ⌈ read ⌉ ⟆
a-redundant-branch = refl

-- the same equation read off the order, which is antisymmetric

weakening-both-ways :
  ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≡ ⟅ ⌈ read ⌉ ⟆
weakening-both-ways = ≾-antisym holds holds

------------------------------------------------------------------------
-- The product does not commute
--
-- A run reading and then writing does not cover writing and then
-- reading, the operations of a guarantee occurring in order.

not-commutative :
  ¬ (⟅ ⌈ read ⌉ ⟆ · ⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⌈ write ⌉ ⟆ · ⟅ ⌈ read ⌉ ⟆)
not-commutative =
  failsᵉ (⟅ ⌈ read ⌉ ⟆ · ⟅ ⌈ write ⌉ ⟆) (⟅ ⌈ write ⌉ ⟆ · ⟅ ⌈ read ⌉ ⟆)
