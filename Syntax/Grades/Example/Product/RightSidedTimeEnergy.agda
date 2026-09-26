------------------------------------------------------------------------
-- Right-sided time paired with an energy budget.                       --
--                                                                     --
-- The energy grade `[0, e ]` says "at most `e` units spent": the       --
-- right-sided intervals' carrier, sum, order, join and `⊤ = [0, ∞ ]`,  --
-- with `of-nat` constantly `[0, ↑ 0 ]`. Idling is free: `delay` spends --
-- time and no energy, and energy is spent by operations alone.         --
--                                                                     --
-- A grade `([0, n ] , [0, e ])` says "at most `n` steps and at most    --
-- `e` units". As a resource grade, a value boxed at it can be unboxed  --
-- only while at most `n` steps have passed and at most `e` units have  --
-- been spent since boxing -- a calibration that drifts with time and   --
-- with use. A variable that is not eternal goes stale after any step   --
-- or any energy spent.                                                 --
--                                                                     --
-- The unit is least and `_·_` commutes; both are declared.             --
------------------------------------------------------------------------

module Syntax.Grades.Example.Product.RightSidedTimeEnergy where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)
open import Syntax.Grades.Example.Time.RightSided
  using ([0,_]; ↑_; ∞; right-sided-intervals)

open import Util.Equality

-- energy: at most so many units, idling free

energy : Grade
energy = record
  { Carrier         = R.Carrier
  ; _·_             = R._·_
  ; u               = R.u
  ; _≾_             = R._≾_
  ; ⊤               = R.⊤
  ; _⊔_             = R._⊔_
  ; of-nat          = λ _ → [0, ↑ 0 ]
  ; ·-identityˡ     = R.·-identityˡ
  ; ·-identityʳ     = R.·-identityʳ
  ; ·-assoc         = R.·-assoc
  ; ≾-refl          = λ {c} → R.≾-refl {c}
  ; ≾-trans         = λ {c} {d} {e} → R.≾-trans {c} {d} {e}
  ; ≾-antisym       = λ {c} {d} → R.≾-antisym {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → R.≾-irrelevant {c} {d}
  ; _≾?_            = R._≾?_
  ; ≾-⊤             = R.≾-⊤
  ; ⊔-ubˡ           = R.⊔-ubˡ
  ; ⊔-ubʳ           = R.⊔-ubʳ
  ; ⊔-lub           = λ {c} {d} {e} → R.⊔-lub {c} {d} {e}
  ; ·-monoˡ-≾       = λ {c} {d} {e} → R.·-monoˡ-≾ {c} {d} {e}
  ; ·-monoʳ-≾       = λ {c} {d} {e} → R.·-monoʳ-≾ {c} {d} {e}
  ; ·-distribˡ-⊔-≾  = R.·-distribˡ-⊔-≾
  ; ·-distribʳ-⊔-≾  = R.·-distribʳ-⊔-≾
  ; ≾-zero-productˡ = λ {c} {d} → R.≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → R.≾-zero-productʳ {c} {d}
  ; of-nat-zero     = refl
  ; of-nat-plus     = refl
  ; u-least?        = R.u-least?
  ; ·-comm?         = R.·-comm?
  }
  where module R = Grade right-sided-intervals

right-sided-time×energy : Grade
right-sided-time×energy = right-sided-intervals ×ᵍ energy

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade right-sided-time×energy

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- a budget of 20 steps and 5 units

budget : Carrier
budget = ([0, ↑ 20 ] , [0, ↑ 5 ])

-- a send: up to 3 steps and 2 units

send : Carrier
send = ([0, ↑ 3 ] , [0, ↑ 2 ])

-- idling is free

idle : of-nat 7 ≡ ([0, ↑ 7 ] , [0, ↑ 0 ])
idle = refl

-- two sends and four idle steps fit the budget

two-sends : send · send · of-nat 4 ≡ ([0, ↑ 10 ] , [0, ↑ 4 ])
two-sends = refl

two-sends-fit : send · send · of-nat 4 ≾ budget
two-sends-fit = ≾! (send · send · of-nat 4) budget

-- three sends are fast enough but spend too much

three-sends-overspend : ¬ (send · send · send ≾ budget)
three-sends-overspend = ⋠! (send · send · send) budget

-- idling for 30 steps spends nothing but misses the deadline

long-idle-late : ¬ (of-nat 30 ≾ budget)
long-idle-late = ⋠! (of-nat 30) budget

-- the greatest grade: no deadline, no energy bound

top : ⊤ ≡ ([0, ∞ ] , [0, ∞ ])
top = refl
