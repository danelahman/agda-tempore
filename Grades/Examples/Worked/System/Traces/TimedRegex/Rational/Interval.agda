-------------------------------------------------------------------------
-- Worked instance: rational timed regex intervals, measured by their  --
-- duration hull.                                                      --
--                                                                     --
-- `System.Traces.TimedRegex.Rational.Interval` measures `[ L , U ]`   --
-- by the lower end of the hull of `L` and the upper end of the hull   --
-- of `U`, each end keeping its side. Heating takes two to four units, --
-- cooling more than one and less than two, logging more than a        --
-- quarter and at most a half. Each measure is computed.               --
-------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.TimedRegex.Rational.Interval where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_,_)

open import Util.Equality

open import Grades.Base using (_→ᵍ_; module Grade)
open _→ᵍ_ using (map)

open import Grades.Examples.Time.Rational.Interval using ([_,_]; ]_,_]; ]_,_[; ↑_; ∞; _/_; #_)
open import Grades.Examples.Worked.Traces.TimedRegex.Finite.Operations
open import Grades.Examples.Traces.TimedRegex.Rational.Interval Op 3 code name name-code code-name running
  using (interval; perform; delay; operation) renaming ([_,_] to [_,_]ᵍ)
open import Grades.Examples.Traces.TimedRegex.Rational.Base Op 3 code name name-code code-name running
  using (⌜_⌝; holds; lower; ε; _·_; ‵_; _⁺ᵉ)
import Grades.Examples.Traces.TimedRegex.Rational.LowerBound Op 3 code name name-code code-name running as L
import Grades.Examples.Traces.TimedRegex.Rational.UpperBound Op 3 code name name-code code-name running as U
open import Grades.Examples.System.Traces.TimedRegex.Rational.Interval Op 3 code name name-code code-name running
  using (timed-regex→intervals)

open Grade interval using (𝟏; ι) renaming (_·_ to _·ᵢ_)

∣_∣ = map timed-regex→intervals

-- heating, a wait of at least two, logging, all within six units of
-- anything: more than four and a quarter units, at most ten and a half

bound-measured :
  ∣ [ ⌜ ‵ heat · L.idle L.≥ (# 2) · ‵ log ⌝ , ⌜ ‵ heat · U.≤ (# 6) · ‵ log ⌝ ]ᵍ ∣
  ≡ ] 17 / 4 , ↑ 21 / 2 ]
bound-measured = refl

-- cooling, then less than a unit: ends open at both sides

cool-measured :
  ∣ [ ⌜ ‵ cool ⌝ , ⌜ ‵ cool · U.< (# 1) ⌝ ]ᵍ ∣ ≡ ] # 1 , ↑ # 3 [
cool-measured = refl

-- a delay is measured by itself, both hulls together

delay-measured : ∣ ι (5 / 2) ∣ ≡ [ 5 / 2 , ↑ 5 / 2 ]
delay-measured = refl

-- heating, a delay of two and a half, logging: inside the bound's window

run-measured : ∣ operation heat ·ᵢ (ι (5 / 2) ·ᵢ operation log) ∣ ≡ ] 19 / 4 , ↑ # 7 ]
run-measured = refl

-- the projection does not reflect the order at the unit: a guarantee of
-- anything under the empty run is measured as the unit, but the
-- guarantee is above the empty one

anything-measured :
  ∣ [ ⌜ L.≥ (# 0) ⌝ , ⌜ ε ⌝ ]ᵍ ∣ ≡ ∣ 𝟏 ∣
anything-measured = refl

anything-above-unit : holds ⌜ L.≥ (# 0) ⌝ ⌜ ε {lower} ⌝ ≡ false
anything-above-unit = refl

-- a cycle of heating and a rest of one to three units, at least once:
-- at least three units, unbounded above

cycle-measured :
  ∣ [ ⌜ ‵ heat · L.idle L.≥ (# 1) ⌝ ⁺ᵉ , ⌜ ‵ heat · U.idle U.≤ (# 3) ⌝ ⁺ᵉ ]ᵍ ∣
  ≡ [ # 3 , ∞ ]
cycle-measured = refl
