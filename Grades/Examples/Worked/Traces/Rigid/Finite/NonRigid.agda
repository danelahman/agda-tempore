------------------------------------------------------------------------
-- Worked: the non-rigid timed trace grades as rigid finite-expression--
-- grades in dense time.                                              --
--                                                                    --
-- The operations of `Rigid.Finite.Operations`: heating takes two to  --
-- four units, cooling more than one and less than two, logging more  --
-- than a quarter and at most a half. An allowance translates an      --
-- operation to `o?` and a delay to a budget `≤ d`; a guarantee an    --
-- operation to `≥0 · o` and a delay to `≥ d`, followed by `≥0`. Each --
-- comparison is decided on both sides by evaluation, and the two     --
-- decisions agree, as `Traces.Timed.ExactGrades` proves they always  --
-- do.                                                                --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.Rigid.Finite.NonRigid where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (isYes)

open import Util.Equality

open import Grades.Base using (Grade)
open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ)
open import Grades.Examples.Time.Dense.TwoSided using (_/_; #_)
open import Grades.Examples.Worked.Traces.Rigid.Finite.Operations
open import Grades.Examples.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running
  using (Upper; ≤_; idle_; ⌜_⌝; Proper′; upper; lower; holds; _·_; _？; ε; expr; _·ᵉ_)
open import Grades.Examples.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running
  using (≥_; ‵_)
open import Grades.Examples.Traces.Rigid.Finite.NonRigid Op 3 code name name-code code-name running

open import Grades.Traces.RunningTimes ℚ≥0ᵀ Op using (module RunningTimes)
open RunningTimes running using (costˡᵒ; costʰⁱ; costʰⁱ-pos)

open import Grades.Traces.Sets ℚ≥0ᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (Trace; ⌈_⌉; ⟨_⟩; _∙_)

import Grades.Examples.Traces.Timed.RightSided
  ℚ≥0ᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos as NR
import Grades.Examples.Traces.Timed.LeftSided
  ℚ≥0ᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ as NL

-- one written-out trace, as a bound and as a guarantee

⟅_⟆ʳ : Trace → NR.Bounds
⟅ t ⟆ʳ = NR.within NR.acSet (t ∷ []) tt

⟅_⟆ˡ : Trace → NL.Antichain
⟅ t ⟆ˡ = NL.acSet (t ∷ []) tt

-- the two decisions of an upper comparison, and of a lower one

upper-both : NR.Bounds → NR.Bounds → Bool × Bool
upper-both P Q = isYes (P NR.≾? Q) , holds (upᴮ P) (upᴮ Q)

lower-both : NL.Antichain → NL.Antichain → Bool × Bool
lower-both P Q = isYes (Grade._≾?_ NL.left-sided P Q) , holds (loᴬ P) (loᴬ Q)

------------------------------------------------------------------------
-- The translations, computed

-- a cooling then two units: cooling may happen, then a budget of two

cool-then-two : expr (upᵉ (⌈ cool ⌉ ∙ ⟨ # 2 ⟩)) ≡ cool ？ · (≤ (# 2) · ε)
cool-then-two = refl

-- as a guarantee: activity, cooling, at least two units, activity

cool-then-two-lower : expr (loᵉ (⌈ cool ⌉ ∙ ⟨ # 2 ⟩)) ≡ ≥ (# 0) · (‵ cool · (≥ (# 2) · ≥ (# 0)))
cool-then-two-lower = refl

------------------------------------------------------------------------
-- Allowances: an operation is charged the upper end of its running
-- time, open or closed

-- cooling, less than two units, fits a budget of two

cool-in-two : upper-both ⟅ ⌈ cool ⌉ ⟆ʳ ⟅ ⟨ # 2 ⟩ ⟆ʳ ≡ (true , true)
cool-in-two = refl

-- but not one of one and a half

cool-not-in-three-halves : upper-both ⟅ ⌈ cool ⌉ ⟆ʳ ⟅ ⟨ 3 / 2 ⟩ ⟆ʳ ≡ (false , false)
cool-not-in-three-halves = refl

-- a budget does not cross an operation the bound keeps

kept-separates : upper-both ⟅ ⌈ log ⌉ ∙ ⟨ # 2 ⟩ ⟆ʳ ⟅ ⟨ # 1 ⟩ ∙ ⌈ log ⌉ ∙ ⟨ # 1 ⟩ ⟆ʳ ≡ (false , false)
kept-separates = refl

-- an operation of the bound the run skips frees nothing, but its
-- budgets on either side join

skipped-joins : upper-both ⟅ ⟨ # 2 ⟩ ⟆ʳ ⟅ ⟨ # 1 ⟩ ∙ ⌈ heat ⌉ ∙ ⟨ # 1 ⟩ ⟆ʳ ≡ (true , true)
skipped-joins = refl

-- a delay of the run is a budget, so it may stand for an operation

heat-for-delay : upper-both ⟅ ⟨ # 4 ⟩ ⟆ʳ ⟅ ⌈ heat ⌉ ⟆ʳ ≡ (false , false)
heat-for-delay = refl

-- the unit is least, and goes to the unit

unit-least : upper-both NR.𝟏ᵇ ⟅ ⌈ heat ⌉ ⟆ʳ ≡ (true , true)
unit-least = refl

-- the unbounded grade goes to the unrestricted stretch, above every
-- written-out bound and below none

unbounded-above : upper-both ⟅ ⟨ # 5 ⟩ ∙ ⌈ heat ⌉ ⟆ʳ NR.unbounded ≡ (true , true)
unbounded-above = refl

------------------------------------------------------------------------
-- Guarantees: an operation is credited the lower end of its running
-- time, open or closed

-- a cooling, more than one unit, guarantees one unit has passed

cool-covers-one : lower-both ⟅ ⌈ cool ⌉ ⟆ˡ ⟅ ⟨ # 1 ⟩ ⟆ˡ ≡ (true , true)
cool-covers-one = refl

-- but not that one and a half have

cool-not-three-halves : lower-both ⟅ ⌈ cool ⌉ ⟆ˡ ⟅ ⟨ 3 / 2 ⟩ ⟆ˡ ≡ (false , false)
cool-not-three-halves = refl

-- time never stands for an operation

time-no-op : lower-both ⟅ ⟨ # 5 ⟩ ⟆ˡ ⟅ ⌈ heat ⌉ ⟆ˡ ≡ (false , false)
time-no-op = refl

-- a demanded wait is met only where it is placed

wait-placed : lower-both ⟅ ⌈ heat ⌉ ∙ ⟨ # 2 ⟩ ⟆ˡ ⟅ ⟨ # 2 ⟩ ∙ ⌈ heat ⌉ ⟆ˡ ≡ (false , false)
wait-placed = refl

-- the unit guarantees nothing, and goes to the greatest grade

unit-greatest : lower-both ⟅ ⌈ heat ⌉ ∙ ⟨ # 2 ⟩ ⟆ˡ NL.𝟏 ≡ (true , true)
unit-greatest = refl

------------------------------------------------------------------------
-- Products and joins

product-commutes :
  holds (upᴮ (⟅ ⌈ cool ⌉ ⟆ʳ NR.·ᵇ ⟅ ⟨ # 1 ⟩ ⟆ʳ)) (upᴮ ⟅ ⌈ cool ⌉ ⟆ʳ ·ᵉ upᴮ ⟅ ⟨ # 1 ⟩ ⟆ʳ)
  ≡ true
product-commutes = refl

product-commutes-lower :
  holds (loᴬ ⟅ ⟨ # 1 ⟩ ⟆ˡ ·ᵉ loᴬ ⟅ ⟨ # 1 ⟩ ⟆ˡ) (loᴬ (⟅ ⟨ # 1 ⟩ ⟆ˡ NL.· ⟅ ⟨ # 1 ⟩ ⟆ˡ))
  ≡ true
product-commutes-lower = refl

------------------------------------------------------------------------
-- The upper map reads a delay as a budget, not as a strict wait: it is
-- a grade morphism into `upperᵇ`, not into `upperᵍ`

budget-not-wait : holds ⌜ ≤ (# 1) ⌝ ⌜ idle ≤ (# 1) ⌝ ≡ false
budget-not-wait = refl
