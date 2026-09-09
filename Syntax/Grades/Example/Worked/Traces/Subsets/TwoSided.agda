------------------------------------------------------------------------
-- Worked instances of the two-sided subset intervals.                 --
--                                                                     --
-- A grade `[ P , Q ]` says `P ⊆ X ⊆ Q`: every run listed in `P` is one --
-- the computation can still exhibit, and every run it has is listed in --
-- `Q`. Both endpoints compare by equality, so the interval is the      --
-- plain one in the subset lattice.                                     --
--                                                                     --
-- The two endpoints are read in opposite directions -- `P`             --
-- conjunctively, `Q` disjunctively -- so weakening drops members below --
-- and adds them above, and the two moves are independent.              --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure.                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Subsets.TwoSided where

open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; [_,_,_]; lo; hi; _◇_; ◇-refl; _·ᵇ_;
         two-sided; _≾ᵇ_; _≾ᵇ?_) public

order : Grade._≾_ two-sided ≡ _≾ᵇ_
order = refl

holds : (i j : TwoSided) {p : True (i ≾ᵇ? j)} → i ≾ᵇ j
holds i j {p} = toWitness p

fails : (i j : TwoSided) {p : False (i ≾ᵇ? j)} → ¬ (i ≾ᵇ j)
fails i j {p} = toWitnessFalse p

-- a deterministic computation is pinned exactly: its one run is both
-- the only one reachable and the only one permitted

exact : (t : Trace) → TwoSided
exact t = [ ⟅ t ⟆ , ⟅ t ⟆ , ◇-refl ⟅ t ⟆ ]

-- a two-branch computation, graded by what its branches do

branching : TwoSided
branching =
  [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]

-- the contract it will be coerced to: a reading must stay reachable,
-- and nothing but those two runs may happen

contract : TwoSided
contract =
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]

------------------------------------------------------------------------
-- Meeting a contract

deterministic-meets-it : exact ⌈ read ⌉ ≾ᵇ contract
deterministic-meets-it = holds _ _

branching-meets-it : branching ≾ᵇ contract
branching-meets-it = holds _ _

-- a computation that cannot read at all fails the floor, though it is
-- well inside the cap

storing-only-fails-the-floor :
  ¬ (exact (⌈ read ⌉ ∙ ⌈ write ⌉) ≾ᵇ contract)
storing-only-fails-the-floor = fails _ _

storing-only-is-inside-the-cap :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᵇ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]
storing-only-is-inside-the-cap = holds _ _

-- and one that transmits fails the cap, though it does read

transmitting-fails-the-cap :
  ¬ (exact ⌈ read ⌉ ·ᵇ exact ⌈ send ⌉ ≾ᵇ contract)
transmitting-fails-the-cap = fails _ _

------------------------------------------------------------------------
-- The endpoints move independently, and in opposite directions
--
-- Below, dropping a member weakens; above, adding one does.

floor-drops-cap-fixed :
  [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]
  ≾ᵇ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]
floor-drops-cap-fixed = holds _ _

cap-gains-floor-fixed :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ]
  ≾ᵇ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ , tt ]
cap-gains-floor-fixed = holds _ _

floor-cannot-gain :
  ¬ ([ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]
     ≾ᵇ branching)
floor-cannot-gain = fails _ _

cap-cannot-drop :
  ¬ ([ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ , tt ]
     ≾ᵇ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ])
cap-cannot-drop = fails _ _

------------------------------------------------------------------------
-- Coherence is exact here
--
-- The field asks `P ⊆ Q`, and that is precisely when some run-set sits
-- between the two: `X := Q` always does. So the field refuses exactly
-- the uninhabited grades -- unlike `Traces.Timed.TwoSided`, whose two
-- endpoints are ordered by incomparable relations and whose field can
-- only be necessary.

demanding-what-is-not-permitted :
  ¬ (traces ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ◇ traces ⟅ ⌈ read ⌉ ⟆)
demanding-what-is-not-permitted ()

-- the widest coherent grade at a given cap demands nothing beyond it

widest-at-a-cap :
  branching
  ≾ᵇ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ , tt ]
widest-at-a-cap = holds _ _

------------------------------------------------------------------------
-- Sequencing
--
-- Both endpoints take the language product, so a branching computation
-- followed by a transmission keeps both completed paths reachable and
-- permits nothing else.

sequencing :
  (branching ·ᵇ exact ⌈ send ⌉)
  ≾ᵇ [ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
sequencing = holds _ _
