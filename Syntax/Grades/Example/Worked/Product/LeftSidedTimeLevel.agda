------------------------------------------------------------------------
-- Worked instances of left-sided time paired with a security level.   --
--                                                                     --
-- The embargo-with-taint-check grade `([ n ,+∞⟩ , ℓ)` at the sensor  --
-- node, each operation graded by `fast` and `touches`: orderings,     --
-- sequencing and the join, checked by the grade's own decision        --
-- procedure or by computation.                                        --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Product.LeftSidedTimeLevel where

open import Data.Maybe.Base using (nothing)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Example.Time.LeftSided using ([_,+∞⟩)
open import Syntax.Grades.Example.SecurityLevel using (Low; High)
open import Syntax.Grades.Example.Product.LeftSidedTimeLevel
  using (left-sided-time×low-high)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; fast)
open import Syntax.Grades.Example.Worked.Operations.Footprint using (touches)

open import Util.Equality

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade left-sided-time×low-high

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- an operation of the sensor node: the time it is guaranteed to take,
-- and the level it touches

node : Op → Carrier
node o = ([ fast o ,+∞⟩ , touches o)

-- the report's box: publishable after 5 steps, from untainted code

report : Carrier
report = ([ 5 ,+∞⟩ , Low)

-- `logged` and two ticks of idling: five steps of `Low` work, and the
-- embargo is over

after-embargo : node read · node write · of-nat 2 ≾ report
after-embargo = ≾! (node read · node write · of-nat 2) report

-- `logged` alone: three steps, still under embargo

under-embargo : ¬ (node read · node write ≾ report)
under-embargo = ⋠! (node read · node write) report

-- `uplink`: seven steps, but it transmits, and is tainted

tainted : ¬ (node read · of-nat 2 · node send ≾ report)
tainted = ⋠! (node read · of-nat 2 · node send) report

-- waiting advances time and leaves the level alone

wait : of-nat 20 ≡ ([ 20 ,+∞⟩ , Low)
wait = refl

-- sequencing adds the time and joins the levels

seq : node read · of-nat 2 · node send ≡ ([ 7 ,+∞⟩ , High)
seq = refl

-- the join keeps the smaller guarantee and the higher level

join : node write ⊔ node send ≡ ([ 2 ,+∞⟩ , High)
join = refl

-- the unit is not declared least

unit-not-least : u-least? ≡ nothing
unit-not-least = refl
