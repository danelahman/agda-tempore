------------------------------------------------------------------------
-- Worked instances of the banked trace intervals.                    --
--                                                                    --
-- A grade `[ P , Q ]` states that whatever the computation did, it   --
-- covered one of the traces in `P` and stayed within one of those in --
-- `Q`. The floor is compared by the coverage order and the cap by    --
-- the allowance order; both sets are read disjunctively, and both    --
-- endpoints weaken by gaining members.                               --
--                                                                    --
-- The two endpoints reject independently: below, five ticks of       --
-- idling are refused by the floor with the cap satisfied, and the    --
-- uplink by the cap with the floor satisfied.                        --
--                                                                    --
-- Each endpoint is measured at its own cost model, the floor at      --
-- `costˡᵒ` (read 1, write 2, send 4) and the cap at `costʰⁱ` (read   --
-- 1, write 3, send 6):                                               --
--                                                                    --
--                                          guaranteed    budgeted    --
--   ⌈ read ⌉                              1 tick        1 tick       --
--   ⟨ 5 ⟩                                 5 ticks       5 ticks      --
--   ⌈ read ⌉ ∙ ⌈ write ⌉                  3 ticks       4 ticks      --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉           7 ticks       9 ticks      --
--                                                                    --
-- The coherence field asks for a run that covers some listed         --
-- guarantee and stays within some listed allowance. It implies that  --
-- the guarantee, measured in the left column, is no greater than the --
-- allowance, measured in the right, and asks more.                   --
--                                                                    --
-- The product does not commute.                                      --
------------------------------------------------------------------------

open import Grades.Durations.Nat using (ℕᵀ)
open import Data.Nat.Properties using (<⇒≢)

module Grades.Examples.Worked.Traces.Banked.Interval where

open import Data.List.Base using ([]; _∷_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costˡᵒ; costʰⁱ; cost-≤;
         costʰⁱ-pos; read; write; send; Trace; ⌈_⌉; ⟨_⟩; _∙_; ε)

open import Grades.Examples.Traces.Banked.Interval
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
  using (Interval; [_,_]; lo; hi; ⊤ᵗˢ; _◇ˢ_; ◇ˢ₀-self; _·ᵗˢ_;
         interval; _≾ᵗˢ_; _≾ᵗˢ?_) public

-- the floor endpoint is an antichain, and is written out the same way

open import Grades.Examples.Traces.Banked.LowerBound
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using () renaming (Antichain to Antichainˡᵒ; traces to tracesˡᵒ;
                     acSet to acSetˡᵒ)

⟅_⟆ˡᵒ : Trace → Antichainˡᵒ
⟅ t ⟆ˡᵒ = acSetˡᵒ (t ∷ []) tt

⟅_∣_⟆ˡᵒ : Trace → Trace → Antichainˡᵒ
⟅ t ∣ u ⟆ˡᵒ = acSetˡᵒ (t ∷ u ∷ []) tt

-- the cap endpoint is an antichain of the allowance side, wrapped in
-- `within_` where `unbounded` could stand instead

open import Grades.Examples.Traces.Banked.UpperBound
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
  using (Bounds; within_; unbounded)
  renaming (Antichain to Antichainʰⁱ; acSet to acSetʰⁱ) public

⟅_⟆ : Trace → Antichainʰⁱ
⟅ t ⟆ = acSetʰⁱ (t ∷ []) tt

⟅_∣_⟆ : Trace → Trace → Antichainʰⁱ
⟅ t ∣ u ⟆ = acSetʰⁱ (t ∷ u ∷ []) tt

order : Grade._≾_ interval ≡ _≾ᵗˢ_
order = refl

holds : (i j : Interval) {p : True (i ≾ᵗˢ? j)} → i ≾ᵗˢ j
holds i j {p} = toWitness p

fails : (i j : Interval) {p : False (i ≾ᵗˢ? j)} → ¬ (i ≾ᵗˢ j)
fails i j {p} = toWitnessFalse p

-- a program with one run has that run at both endpoints

exact : (t : Trace) → Interval
exact t = [ ⟅ t ⟆ˡᵒ , within ⟅ t ⟆ ] {◇ˢ₀-self (tracesˡᵒ ⟅ t ⟆ˡᵒ) tt}

------------------------------------------------------------------------
-- A contract, and which programs meet it
--
-- "Took a reading, and did no more than a reading and six ticks'
-- worth of work."

polling :
  exact ⌈ read ⌉ ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
polling = holds _ _

logging :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
logging = holds _ _

-- idling is refused by the floor: it takes no reading, though it stays
-- well inside the allowance

idling :
  ¬ (exact ⟨ 5 ⟩ ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ])
idling = fails _ _

idling-stays-inside :
  exact ⟨ 5 ⟩ ≾ᵗˢ [ ⟅ ε ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
idling-stays-inside =
  holds (exact ⟨ 5 ⟩) [ ⟅ ε ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]

-- and the uplink by the cap: it takes a reading, but two ticks and a
-- transmission need eight, not six

uplinking :
  ¬ (exact (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ])
uplinking = fails _ _

uplinking-guarantees-the-reading :
  exact (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 8 ⟩ ⟆ ]
uplinking-guarantees-the-reading = holds _ _

------------------------------------------------------------------------
-- Sub-effecting moves the two endpoints independently

guarantee-less :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ]
guarantee-less = holds _ _

permit-more :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
permit-more = holds _ _

-- and neither may be reversed

no-stronger-guarantee :
  ¬ (exact ⌈ read ⌉
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ])
no-stronger-guarantee = fails _ _

no-tighter-allowance :
  ¬ (exact (⌈ read ⌉ ∙ ⌈ write ⌉)
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ⟆ ])
no-tighter-allowance = fails _ _

------------------------------------------------------------------------
-- One trace fact, two directions
--
-- The store is extra work relative to the reading, and both orders
-- relate the two runs the same way round:
--
--   ⌈ read ⌉ ≼ᶜ ⌈ read ⌉ ∙ ⌈ write ⌉    a run that stores still covers
--                                        "a reading was taken"
--   ⌈ read ⌉ ≼ᵃ ⌈ read ⌉ ∙ ⌈ write ⌉    a bound naming a store still
--                                        permits reading and stopping
--
-- The floor's lift reverses and the cap's does not, so the one fact
-- reads as weakening at the floor and as loosening at the cap.

-- at the floor, with the cap held fixed: the store may be dropped from
-- what is guaranteed

guarantee-survives-the-store :
  [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
guarantee-survives-the-store = holds _ _

-- and not upwards: a guarantee is never strengthened by weakening

guarantee-cannot-gain-the-store :
  ¬ ([ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ])
guarantee-cannot-gain-the-store = fails _ _

-- at the cap, with the floor held fixed and the same two runs: the
-- store may be added to what is permitted

allowance-admits-the-store :
  [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ⟆ ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ]
allowance-admits-the-store = holds _ _

-- and not the other way: extra work breaks an allowance, which is the
-- asymmetry the two orders exist to keep apart

allowance-broken-by-the-store :
  ¬ ([ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ]
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ⟆ ])
allowance-broken-by-the-store = fails _ _

-- the two moves compose: a computation known to read and store exactly
-- reaches a contract guaranteeing only the reading and permitting six
-- further ticks, the floor weakening while the cap loosens

read-then-store-meets-the-contract :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
read-then-store-meets-the-contract = holds _ _

-- what cannot be done is to put the two runs at the endpoints the other
-- way round: guaranteeing the store under an allowance of a reading
-- alone is refused by the coherence field, no run that stores staying
-- within a reading

inverted-is-not-a-grade :
  ¬ (tracesˡᵒ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ˡᵒ ◇ˢ within ⟅ ⌈ read ⌉ ⟆)
inverted-is-not-a-grade ()

------------------------------------------------------------------------
-- Both endpoints gain members
--
-- Adding a listed trace weakens at either end, the sets being read
-- disjunctively, so a branching computation is graded by listing what
-- each branch does, at both endpoints.

add-a-guarantee :
  [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
add-a-guarantee = holds _ _

add-an-allowance :
  [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ]
add-an-allowance = holds _ _

branches :
  [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ˡᵒ
  , within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ˡᵒ
      , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ]
branches = holds _ _

------------------------------------------------------------------------
-- Sequencing, and the coherence field
--
-- The field asks for a run consistent with a listed guarantee and a
-- listed allowance. It holds of every grade above, is preserved by
-- sequencing, and rules out pairs no run could satisfy.

sequencing :
  (exact ⌈ read ⌉ ·ᵗˢ exact ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]
sequencing = holds _ _

-- a floor that takes ten ticks under a cap that permits one is not a
-- grade at all: there is no run it could admit

no-such-interval :
  ¬ (tracesˡᵒ ⟅ ⟨ 10 ⟩ ⟆ˡᵒ ◇ˢ within ⟅ ⌈ read ⌉ ⟆)
no-such-interval ()

-- durations alone do not settle it: a store guaranteed in two ticks
-- fits three readings' worth of budget, but a bound naming only
-- readings, and no delay, leaves nothing to pay for a store with

no-run-stores-within-readings :
  ¬ (tracesˡᵒ ⟅ ⌈ write ⌉ ⟆ˡᵒ ◇ˢ within ⟅ ⌈ read ⌉ ∙ ⌈ read ⌉ ∙ ⌈ read ⌉ ⟆)
no-run-stores-within-readings ()

-- and a run may meet a guarantee of time with an operation the bound
-- names: the store takes at least two ticks, so performing it covers
-- two ticks of idling

store-covers-two-ticks : Interval
store-covers-two-ticks = [ ⟅ ⟨ 2 ⟩ ⟆ˡᵒ , within ⟅ ⌈ write ⌉ ⟆ ]

------------------------------------------------------------------------
-- The greatest grade
--
-- `⊤ᵗˢ` is the weakest guarantee, which is the unit, under an
-- unbounded allowance. Sequencing absorbs at the cap alone; the floor
-- keeps whatever the other factor guarantees.

everything-weakens-to-the-top :
  [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ] ≾ᵗˢ ⊤ᵗˢ
everything-weakens-to-the-top =
  holds [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ] ⊤ᵗˢ

the-top-weakens-to-nothing-else :
  ¬ (⊤ᵗˢ ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ])
the-top-weakens-to-nothing-else =
  fails ⊤ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]

the-cap-absorbs :
  hi (⊤ᵗˢ ·ᵗˢ exact ⌈ read ⌉) ≡ unbounded
the-cap-absorbs = refl


------------------------------------------------------------------------
-- The product does not commute
--
-- Reading and then writing does not meet both ends of writing and then
-- reading.

not-commutative :
  ¬ (exact ⌈ read ⌉ ·ᵗˢ exact ⌈ write ⌉ ≾ᵗˢ exact ⌈ write ⌉ ·ᵗˢ exact ⌈ read ⌉)
not-commutative = fails _ _
