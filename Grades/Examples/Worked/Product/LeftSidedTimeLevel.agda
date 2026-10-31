------------------------------------------------------------------------
-- Worked instances of left-sided time paired with a security level.  --
--                                                                    --
-- The embargo-with-taint-check grade `([ n ,+∞⟩ , ℓ)` at the sensor  --
-- node, each operation graded by `fast` and `touches`: orderings,    --
-- sequencing and the join, established by the decision procedure of  --
-- the grade or by computation.                                       --
------------------------------------------------------------------------

module Grades.Examples.Worked.Product.LeftSidedTimeLevel where

open import Data.Product using (_,_)

open import Relation.Binary.Definitions using (Minimum)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)
open import Grades.Examples.Time.LeftSided using ([_,+∞⟩)
open import Grades.Examples.SecurityLevel using (Low; High)
open import Grades.Examples.Product.LeftSidedTimeLevel
  using (left-sided-time×low-high)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; fast)
open import Grades.Examples.Worked.Operations.Footprint using (touches)

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

after-embargo : node read · node write · ι 2 ≾ report
after-embargo = ≾! (node read · node write · ι 2) report

-- `logged` alone: three steps, still under embargo

under-embargo : ¬ (node read · node write ≾ report)
under-embargo = ⋠! (node read · node write) report

-- `uplink`: seven steps, but it transmits, and is tainted

tainted : ¬ (node read · ι 2 · node send ≾ report)
tainted = ⋠! (node read · ι 2 · node send) report

-- waiting advances time and leaves the level alone

wait : ι 20 ≡ ([ 20 ,+∞⟩ , Low)
wait = refl

-- sequencing adds the time and joins the levels

seq : node read · ι 2 · node send ≡ ([ 7 ,+∞⟩ , High)
seq = refl

-- the join keeps the smaller guarantee and the higher level

join : node write ⊔ node send ≡ ([ 2 ,+∞⟩ , High)
join = refl

-- the unit is not least: it is not below an embargo

unit-not-least : ¬ Minimum _≾_ 𝟏
unit-not-least least = ⋠! 𝟏 ([ 1 ,+∞⟩ , Low) (least ([ 1 ,+∞⟩ , Low))
