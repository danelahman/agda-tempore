------------------------------------------------------------------------
-- Rigid timed regular grades in whole steps, as intervals.           --
--                                                                    --
-- A grade `[ L , U ]` pairs a lower bound with an upper bound,       --
-- compared componentwise: the product of the two grades. A delay     --
-- advances both components.                                          --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᴰ; ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Regular.TwoSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Product using (_×_; _,_)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)

import Syntax.Grades.Example.Traces.Rigid.Regular.LeftSided Op n code name name-code code-name running as L
import Syntax.Grades.Example.Traces.Rigid.Regular.RightSided Op n code name name-code code-name running as U

open L public using (Closed; Lower; !≥_; !>_; ≥_; >_)
open U public using (Upper; !≤_; !<_; ≤_; <_; ≤∞)

two-sided : Grade ℕᴰ
two-sided = L.left-sided ×ᵍ U.right-sided

-- a pair of literals

[_,_] : Closed → Closed → Closed × Closed
[ l , u ] = l , u
