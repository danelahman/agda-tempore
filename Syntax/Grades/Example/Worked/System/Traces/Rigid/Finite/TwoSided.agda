------------------------------------------------------------------------
-- Worked instance: rigid finite-expression intervals, measured by    --
-- their duration hull.                                               --
--                                                                    --
-- `System.Traces.Rigid.Finite.TwoSided` measures `[ L , U ]` by the  --
-- lower end of the hull of `L` and the upper end of the hull of `U`, --
-- each end keeping its side. Heating takes two to four units,        --
-- cooling more than one and less than two, logging more than a       --
-- quarter and at most a half. Each measure is computed.              --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Traces.Rigid.Finite.TwoSided where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_,_)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_; module Grade)
open _→ᵍ_ using (map)

open import Syntax.Grades.Example.Time.Dense.TwoSided using ([_,_]; ]_,_]; ]_,_[; ↑_; _/_; #_)
open import Syntax.Grades.Example.Worked.Traces.Rigid.Finite.Operations
open import Syntax.Grades.Example.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
  using (two-sided; [_,_]⟨_⟩; perform; delay; operation)
open import Syntax.Grades.Example.Traces.Rigid.Finite.Base Op 3 code name name-code code-name running
  using (⌜_⌝; holds; lower; ε; _·_; ‵_)
import Syntax.Grades.Example.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running as L
import Syntax.Grades.Example.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running as U
open import Syntax.Grades.Example.System.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
  using (interval-runs→intervals)

open Grade two-sided using (u; of-dur) renaming (_·_ to _·ᵢ_)

∣_∣ = map interval-runs→intervals

-- heating, a wait of at least two, logging, all within six units of
-- anything: more than four and a quarter units, at most ten and a half

bound-measured :
  ∣ [ ⌜ ‵ heat · L.!≥ (# 2) · ‵ log ⌝ , ⌜ ‵ heat · U.≤ (# 6) · ‵ log ⌝ ]⟨
      perform heat ∷ delay (# 2) ∷ perform log ∷ [] ⟩ ∣
  ≡ ] 17 / 4 , ↑ 21 / 2 ]
bound-measured = refl

-- cooling, then less than a unit: ends open at both sides

cool-measured :
  ∣ [ ⌜ ‵ cool ⌝ , ⌜ ‵ cool · U.< (# 1) ⌝ ]⟨ perform cool ∷ [] ⟩ ∣ ≡ ] # 1 , ↑ # 3 [
cool-measured = refl

-- a delay is measured by itself, both hulls together

delay-measured : ∣ of-dur (5 / 2) ∣ ≡ [ 5 / 2 , ↑ 5 / 2 ]
delay-measured = refl

-- heating, a delay of two and a half, logging: inside the bound's window

run-measured : ∣ operation heat ·ᵢ (of-dur (5 / 2) ·ᵢ operation log) ∣ ≡ ] 19 / 4 , ↑ # 7 ]
run-measured = refl

-- the projection does not reflect the order at the unit: a guarantee of
-- anything under the empty run is measured as the unit, but the
-- guarantee is above the empty one

anything-measured :
  ∣ [ ⌜ L.≥ (# 0) ⌝ , ⌜ ε ⌝ ]⟨ [] ⟩ ∣ ≡ ∣ u ∣
anything-measured = refl

anything-above-unit : holds ⌜ L.≥ (# 0) ⌝ ⌜ ε {lower} ⌝ ≡ false
anything-above-unit = refl
