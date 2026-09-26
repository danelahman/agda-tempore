------------------------------------------------------------------------
-- Worked instances of left-sided time paired with a security level.   --
--                                                                     --
-- The embargo-with-taint-check grade `([ n ,+∞⟩ , ℓ)`: orderings,      --
-- sequencing and the join, checked by the grade's own decision         --
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

open import Util.Equality

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade left-sided-time×low-high

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- the report's box: publishable after 30 steps, from untainted code

report : Carrier
report = ([ 30 ,+∞⟩ , Low)

-- 45 steps of `Low` work: the embargo is over

after-embargo : ([ 45 ,+∞⟩ , Low) ≾ report
after-embargo = ≾! ([ 45 ,+∞⟩ , Low) report

-- 20 steps: still under embargo

under-embargo : ¬ (([ 20 ,+∞⟩ , Low) ≾ report)
under-embargo = ⋠! ([ 20 ,+∞⟩ , Low) report

-- 45 steps that read `High` data: tainted

tainted : ¬ (([ 45 ,+∞⟩ , High) ≾ report)
tainted = ⋠! ([ 45 ,+∞⟩ , High) report

-- waiting advances time and leaves the level alone

wait : of-nat 20 ≡ ([ 20 ,+∞⟩ , Low)
wait = refl

-- sequencing adds the time and joins the levels

seq : of-nat 20 · ([ 1 ,+∞⟩ , High) ≡ ([ 21 ,+∞⟩ , High)
seq = refl

-- the join keeps the smaller guarantee and the higher level

join : ([ 10 ,+∞⟩ , Low) ⊔ ([ 20 ,+∞⟩ , High) ≡ ([ 10 ,+∞⟩ , High)
join = refl

-- the unit is not declared least

unit-not-least : u-least? ≡ nothing
unit-not-least = refl
