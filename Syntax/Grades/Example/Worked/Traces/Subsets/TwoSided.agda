------------------------------------------------------------------------
-- Worked instances of the two-sided subset intervals.                 --
--                                                                     --
-- A grade `[ P , Q ]` says `P ⊆ X ⊆ Q`: every run listed in `P` is one --
-- the computation can still exhibit, and every run it has is listed in --
-- `Q`. Both endpoints compare by equality, so the interval is the      --
-- plain one in the subset lattice. Above all such pairs sits           --
-- `unconstrained`, which demands nothing and permits everything.       --
--                                                                     --
-- The two endpoints are read in opposite directions -- `P`             --
-- conjunctively, `Q` disjunctively -- so weakening drops members below --
-- and adds them above, and the two moves are independent.              --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure.                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Subsets.TwoSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; [_,_,_]; lo; hi; _◇_; ◇-refl;
         Interval; between_; unconstrained; _·ᴵ_;
         two-sided; _≾ᴵ_; _≾ᴵ?_) public

order : Grade._≾_ two-sided ≡ _≾ᴵ_
order = refl

holds : (i j : Interval) {p : True (i ≾ᴵ? j)} → i ≾ᴵ j
holds i j {p} = toWitness p

fails : (i j : Interval) {p : False (i ≾ᴵ? j)} → ¬ (i ≾ᴵ j)
fails i j {p} = toWitnessFalse p

-- a written-out pair of run lists is a grade under `between`, its
-- decided coherence field left implicit

⟪_,_⟫ : (P Q : NeTraces) {coh : traces P ◇ traces Q} → Interval
⟪ P , Q ⟫ {coh} = between [ P , Q , coh ]

-- a deterministic computation is pinned exactly: its one run is both
-- the only one reachable and the only one permitted

exact : (t : Trace) → Interval
exact t = between [ ⟅ t ⟆ , ⟅ t ⟆ , ◇-refl ⟅ t ⟆ ]

-- a two-branch computation, graded by what its branches do

branching : Interval
branching =
  ⟪ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ⟫

-- the contract it will be coerced to: a reading must stay reachable,
-- and nothing but those two runs may happen

contract : Interval
contract =
  ⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ⟫

------------------------------------------------------------------------
-- Meeting a contract

deterministic-meets-it : exact ⌈ read ⌉ ≾ᴵ contract
deterministic-meets-it = holds _ _

branching-meets-it : branching ≾ᴵ contract
branching-meets-it = holds _ _

-- a computation that cannot read at all fails the floor, though it is
-- well inside the cap

storing-between-fails-the-floor :
  ¬ (exact (⌈ read ⌉ ∙ ⌈ write ⌉) ≾ᴵ contract)
storing-between-fails-the-floor = fails _ _

storing-between-is-inside-the-cap :
  exact (⌈ read ⌉ ∙ ⌈ write ⌉)
  ≾ᴵ ⟪ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ⟫
storing-between-is-inside-the-cap = holds _ _

-- and one that transmits fails the cap, though it does read

transmitting-fails-the-cap :
  ¬ (exact ⌈ read ⌉ ·ᴵ exact ⌈ send ⌉ ≾ᴵ contract)
transmitting-fails-the-cap = fails _ _

------------------------------------------------------------------------
-- The endpoints move independently, and in opposite directions
--
-- Below, dropping a member weakens; above, adding one does.

floor-drops-cap-fixed :
  ⟪ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
  , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ⟫
  ≾ᴵ ⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ⟫
floor-drops-cap-fixed = holds _ _

cap-gains-floor-fixed :
  ⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ ⟫
  ≾ᴵ ⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ ⟫
cap-gains-floor-fixed = holds _ _

floor-cannot-gain :
  ¬ (⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ⟫
     ≾ᴵ branching)
floor-cannot-gain = fails _ _

cap-cannot-drop :
  ¬ (⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ ⟫
     ≾ᴵ ⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ ⟫)
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
  ≾ᴵ ⟪ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆ ⟫
widest-at-a-cap = holds _ _

------------------------------------------------------------------------
-- Sequencing
--
-- Both endpoints take the language product, so a branching computation
-- followed by a transmission keeps both completed paths reachable and
-- permits nothing else.

sequencing :
  (branching ·ᴵ exact ⌈ send ⌉)
  ≾ᴵ ⟪ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ ⟫
sequencing = holds _ _

------------------------------------------------------------------------
-- The greatest grade
--
-- No pair is greatest: the floor's would demand nothing, which is the
-- empty set and excluded. `unconstrained` is that pair's stand-in -- it
-- demands nothing and permits everything -- and it is absorbing.

everything-weakens-to-the-top :
  contract ≾ᴵ unconstrained
everything-weakens-to-the-top = holds contract unconstrained

the-top-weakens-to-no-pair :
  ¬ (unconstrained ≾ᴵ contract)
the-top-weakens-to-no-pair = fails unconstrained contract

the-top-absorbs :
  (unconstrained ·ᴵ contract) ≡ unconstrained
the-top-absorbs = refl
