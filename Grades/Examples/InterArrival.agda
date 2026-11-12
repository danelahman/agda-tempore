------------------------------------------------------------------------
-- Inter-arrival grades: how often each operation recurs, bounding    --
-- the times before, between and after its calls, over a time domain  --
-- and a set of operation names.                                      --
--                                                                    --
-- For one operation, a run is either silent, calling it not at all   --
-- for a duration `d`, or active, calling it `k ≥ 1` times, with a    --
-- lead time `a` before the first call, the gaps between the starts   --
-- of consecutive calls, and a tail `b` from the start of the last    --
-- call to the end. Sequencing adds a silent duration to the adjacent --
-- lead time or tail, and joins two active parts with a new gap, the  --
-- tail of the first and the lead time of the second                  --
-- (`InterArrival.Entry`).                                            --
--                                                                    --
-- A grade bounds, for each operation, the silent durations, the      --
-- counts, the lead times, the gaps and the tails by intervals, a     --
-- case possibly absent, together with the total duration of the run, --
-- which all operations share. It is the grade of one operation       --
-- indexed by the names (`Grades.Indexed`), paired with the intervals --
-- of the total duration (`Grades.Product`): the order compares ends, --
-- joins are hulls, the unit is silent for no time at every name and  --
-- takes no time, and a delay by `τ` is silent for `τ` at every name  --
-- and takes `τ`.                                                     --
--                                                                    --
-- The unit is not least and the product does not commute             --
-- (`Grades.Examples.Worked.InterArrival`). The closures are those of --
-- the entries, name by name (`InterArrival.Closure`), paired with    --
-- those of the intervals of the total duration.                      --
------------------------------------------------------------------------

open import Grades.Durations
open import Grades.Indexed using (DecNames)

module Grades.Examples.InterArrival {D : Duration} (T : TimeDomain D) (𝒩 : DecNames) where

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_×_; _,_)

open import Grades.Base
open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Indexed using (module Maps)
import Grades.Examples.Time.Interval as C
open import Grades.Examples.Time.Intervals T using (domain-interval; domain-intervalʰ; Interval; 0ⁱ)

open import Grades.Examples.InterArrival.Entry T public
open import Grades.Examples.InterArrival.Closure T public

open DecNames 𝒩 using (Name)
open Maps 𝒩 using (Map; _∣_; _!_; everywhere; indexedᵍ; indexedʰ) public

------------------------------------------------------------------------
-- The grade

inter-arrival : Grade D
inter-arrival = indexedᵍ entryᵍ ×ᵍ domain-interval

-- its hints: the closures are those of the entries, name by name,
-- paired with those of the total duration; neither that the unit is
-- least nor that the product commutes is declared, as neither holds

inter-arrivalʰ : GradeHints inter-arrival
inter-arrivalʰ = record
  { 𝟏-least? = nothing
  ; ·-comm?  = nothing
  ; plus?    = GradeHints.plus? (indexedʰ entryᵍ entryʰ ×ʰ domain-intervalʰ)
  }

------------------------------------------------------------------------
-- Grades of computations

-- a computation calling no operation and taking a duration in `i`

delays : Interval → Map Entry × Interval
delays i = everywhere (entry (just i) nothing) , i

-- one call of the operation `x`, taking a duration in `i`: active at
-- `x`, once, at once, its tail the running time, and silent at the
-- other names

occurrence : Name → Interval → Map Entry × Interval
occurrence x i =
  (entry (just i) nothing ∣ ((x , entry nothing (just (act C.[ 1 , C.↑ 1 ] 0ⁱ nothing i))) ∷ []))
  , i
