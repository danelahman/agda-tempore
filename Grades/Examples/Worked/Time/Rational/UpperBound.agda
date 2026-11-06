------------------------------------------------------------------------
-- Worked instances of the dense upper-bound grade.                   --
--                                                                    --
-- "At most `q` units", a real-time deadline: orderings between       --
-- concrete grades, each established by the decision procedure of the --
-- grade; sequencing and absorption, computed.                        --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Rational.UpperBound where

open import Relation.Nullary using (¬_)

open import Util.Equality

import Grades.Examples.Time.Rational.UpperBound as R

open import Grades.Examples.Time.Rational.ExtendedRational
  using (↑_; ∞; _/_; #_; nonZero)

open import Grades.Examples.Worked.Time.Rational.Decide using (module Decide)

open Decide R.rational-upper-bound renaming (≾! to ≾ʳ!; ⋠! to ⋠ʳ!)

------------------------------------------------------------------------
-- Upper-bound: "at most q units", a real-time deadline

-- meeting a deadline of 2.5 units meets one of 3

upper-weaken : R.[0, ↑ 5 / 2 ] R.≾ₒ R.[0, ↑ # 3 ]
upper-weaken = ≾ʳ!

upper-no-strengthen : ¬ (R.[0, ↑ # 3 ] R.≾ₒ R.[0, ↑ 5 / 2 ])
upper-no-strengthen = ⋠ʳ!

-- every deadline is below having none

upper-top : R.[0, ↑ 5 / 2 ] R.≾ₒ R.[0, ∞ ]
upper-top = ≾ʳ! {R.[0, ↑ 5 / 2 ]} {R.[0, ∞ ]}

-- deadlines add: 1/2 + 2/3 = 7/6

upper-add : R.[0, ↑ 1 / 2 ] R.·ₒ R.[0, ↑ 2 / 3 ] ≡ R.[0, ↑ 7 / 6 ]
upper-add = refl

-- an unbounded computation stays unbounded

upper-absorb : R.[0, ↑ 1 / 2 ] R.·ₒ R.[0, ∞ ] ≡ R.[0, ∞ ]
upper-absorb = refl
