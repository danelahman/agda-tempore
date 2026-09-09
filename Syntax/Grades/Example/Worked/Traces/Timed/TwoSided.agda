------------------------------------------------------------------------
-- Worked instances of the two-sided trace intervals.                  --
--                                                                     --
-- A grade `[ P , Q ]` says: whatever the computation did, it covered   --
-- one of the traces in `P` and stayed within one of those in `Q`. The  --
-- floor is compared by the coverage order and the cap by the allowance --
-- order, and both sets are read disjunctively, so both endpoints       --
-- weaken by gaining members.                                          --
--                                                                     --
-- The point of having both is that they reject for independent         --
-- reasons: below, five ticks of idling are refused by the floor with   --
-- the cap satisfied, and the uplink by the cap with the floor          --
-- satisfied.                                                          --
--                                                                     --
-- Under `cost` -- read 1, write 3, send 6 -- the runs below take       --
--                                                                     --
--   ⌈ read ⌉                             1 tick                       --
--   ⟨ 5 ⟩                                5 ticks                      --
--   ⌈ read ⌉ ∙ ⌈ write ⌉                 4 ticks                      --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉          9 ticks                      --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Timed.TwoSided where

open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.Timed.TwoSided Op _≟ₒ_ cost cost-pos
  using (TwoSided; [_,_,_]; lo; hi; _◇ˢ_; ◇ˢ-refl; _·ᵗˢ_;
         two-sided; _≾ᵗˢ_; _≾ᵗˢ?_) public

order : Grade._≾_ two-sided ≡ _≾ᵗˢ_
order = refl

holds : (i j : TwoSided) {p : True (i ≾ᵗˢ? j)} → i ≾ᵗˢ j
holds i j {p} = toWitness p

fails : (i j : TwoSided) {p : False (i ≾ᵗˢ? j)} → ¬ (i ≾ᵗˢ j)
fails i j {p} = toWitnessFalse p

-- a program with one run has that run at both endpoints

exact : (t : Trace) → TwoSided
exact t = [ ⟅ t ⟆ , ⟅ t ⟆ , ◇ˢ-refl ⟅ t ⟆ ]

------------------------------------------------------------------------
-- A contract, and which programs meet it
--
-- "Took a reading, and did no more than a reading and six ticks'
-- worth of work."

polling :
  exact ⌈ read ⌉ ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
polling = holds _ _

logging :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
logging = holds _ _

-- idling is refused by the floor: it takes no reading, though it stays
-- well inside the allowance

idling :
  ¬ (exact ⟨ 5 ⟩ ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ])
idling = fails _ _

idling-stays-inside :
  exact ⟨ 5 ⟩ ≾ᵗˢ [ ⟅ ε ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
idling-stays-inside =
  holds (exact ⟨ 5 ⟩) [ ⟅ ε ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]

-- and the uplink by the cap: it takes a reading, but two ticks and a
-- transmission need eight, not six

uplinking :
  ¬ (exact (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ])
uplinking = fails _ _

uplinking-guarantees-the-reading :
  exact (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 8 ⟩ ⟆ , tt ]
uplinking-guarantees-the-reading = holds _ _

------------------------------------------------------------------------
-- Sub-effecting moves the two endpoints independently

guarantee-less :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]
guarantee-less = holds _ _

permit-more :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
permit-more = holds _ _

-- and neither may be reversed

no-stronger-guarantee :
  ¬ (exact ⌈ read ⌉
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ])
no-stronger-guarantee = fails _ _

no-narrower-allowance :
  ¬ (exact (⌈ read ⌉ ∙ ⌈ write ⌉)
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ])
no-narrower-allowance = fails _ _

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
-- The two endpoints nonetheless move in opposite directions, because
-- the floor's lift reverses and the cap's does not. So the single fact
-- "the store is extra work" reads as *weakening* at the floor and as
-- *widening* at the cap.

-- at the floor, with the cap held fixed: the store may be dropped from
-- what is guaranteed

guarantee-survives-the-store :
  [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
guarantee-survives-the-store = holds _ _

-- and not upwards: a guarantee is never strengthened by weakening

guarantee-cannot-gain-the-store :
  ¬ ([ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ])
guarantee-cannot-gain-the-store = fails _ _

-- at the cap, with the floor held fixed and the same two runs: the
-- store may be added to what is permitted

allowance-admits-the-store :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]
allowance-admits-the-store = holds _ _

-- and not the other way: extra work breaks an allowance, which is the
-- asymmetry the two orders exist to keep apart

allowance-broken-by-the-store :
  ¬ ([ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]
     ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ])
allowance-broken-by-the-store = fails _ _

-- the two moves compose: a computation known to read and store exactly
-- reaches a contract guaranteeing only the reading and permitting six
-- further ticks, the floor weakening while the cap widens

read-then-store-meets-the-contract :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
read-then-store-meets-the-contract = holds _ _

-- what cannot be done is to put the two runs at the endpoints the other
-- way round: guaranteeing the store under an allowance of a reading
-- alone is refused by the coherence field, four ticks being no less
-- than one

inverted-is-not-a-grade :
  ¬ (traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ◇ˢ traces ⟅ ⌈ read ⌉ ⟆)
inverted-is-not-a-grade ()

------------------------------------------------------------------------
-- Both endpoints gain members
--
-- Adding a listed trace weakens at either end, the sets being read
-- disjunctively -- so a branching computation is graded by listing what
-- each branch does, at both endpoints.

add-a-guarantee :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
add-a-guarantee = holds _ _

add-an-allowance :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
add-an-allowance = holds _ _

branches :
  [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆
      , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
branches = holds _ _

------------------------------------------------------------------------
-- Sequencing, and the coherence field
--
-- The field asks some listed guarantee to take no longer than some
-- listed allowance. It holds of every grade above, is preserved by
-- sequencing, and rules out pairs no run could satisfy.

sequencing :
  (exact ⌈ read ⌉ ·ᵗˢ exact ⌈ write ⌉)
  ≾ᵗˢ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ , tt ]
sequencing = holds _ _

-- a floor that takes ten ticks under a cap that permits one is not a
-- grade at all: there is no run it could admit

no-such-interval :
  ¬ (traces ⟅ ⟨ 10 ⟩ ⟆ ◇ˢ traces ⟅ ⌈ read ⌉ ⟆)
no-such-interval ()
