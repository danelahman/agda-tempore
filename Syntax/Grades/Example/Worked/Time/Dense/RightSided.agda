------------------------------------------------------------------------
-- Worked instances of the dense right-sided grade.                   --
--                                                                    --
-- "At most `q` units", a real-time deadline: orderings between       --
-- concrete grades, each established by the decision procedure of the --
-- grade; sequencing and absorption, computed.                        --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Time.Dense.RightSided where

open import Relation.Nullary using (¬_)

open import Util.Equality

import Syntax.Grades.Example.Time.Dense.RightSided as R

open import Syntax.Grades.Example.Time.Dense.ExtendedRational
  using (↑_; ∞; _/_; #_; nonZero)

open import Syntax.Grades.Example.Worked.Time.Dense.Decide using (module Decide)

open Decide R.dense-right-sided-intervals renaming (≾! to ≾ʳ!; ⋠! to ⋠ʳ!)

------------------------------------------------------------------------
-- Right-sided: "at most q units", a real-time deadline

-- meeting a deadline of 2.5 units meets one of 3

rsi-weaken : R.[0, ↑ 5 / 2 ] R.≾ₒ R.[0, ↑ # 3 ]
rsi-weaken = ≾ʳ!

rsi-no-strengthen : ¬ (R.[0, ↑ # 3 ] R.≾ₒ R.[0, ↑ 5 / 2 ])
rsi-no-strengthen = ⋠ʳ!

-- every deadline is below having none

rsi-top : R.[0, ↑ 5 / 2 ] R.≾ₒ R.[0, ∞ ]
rsi-top = ≾ʳ! {R.[0, ↑ 5 / 2 ]} {R.[0, ∞ ]}

-- deadlines add: 1/2 + 2/3 = 7/6

rsi-add : R.[0, ↑ 1 / 2 ] R.·ₒ R.[0, ↑ 2 / 3 ] ≡ R.[0, ↑ 7 / 6 ]
rsi-add = refl

-- an unbounded computation stays unbounded

rsi-absorb : R.[0, ↑ 1 / 2 ] R.·ₒ R.[0, ∞ ] ≡ R.[0, ∞ ]
rsi-absorb = refl
