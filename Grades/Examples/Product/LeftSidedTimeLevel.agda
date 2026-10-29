------------------------------------------------------------------------
-- Left-sided time paired with a security level.                      --
--                                                                    --
-- A grade `([ n ,+∞⟩ , ℓ)` states "at least `n` time steps, touching --
-- nothing above `ℓ`". A time step advances the first component only. --
--                                                                    --
-- As a resource grade it is an embargo with a taint check: a value   --
-- boxed at `([ n ,+∞⟩ , ℓ)` can be unboxed once at least `n` steps   --
-- have passed since boxing, and only while nothing above `ℓ` has     --
-- been touched since, as for a report that may be published after an --
-- embargo and only from untainted code. The left-sided unit is       --
-- greatest, so time alone never makes a variable stale; touching     --
-- `High` does.                                                       --
--                                                                    --
-- The unit is not least, as for left-sided time; `_·_` commutes, as  --
-- its hints declare.                                                 --
------------------------------------------------------------------------

module Grades.Examples.Product.LeftSidedTimeLevel where

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Examples.Time.LeftSided using (left-sided-intervals; left-sided-intervalsʰ)
open import Grades.Examples.SecurityLevel
  using (LevelLattice; level-grade; level-gradeʰ; low-high)

-- left-sided time and a lattice of levels

left-sided-time×level : LevelLattice → Grade ℕᴰ
left-sided-time×level L = left-sided-intervals ×ᵍ level-grade L

left-sided-time×levelʰ : (L : LevelLattice) → GradeHints (left-sided-time×level L)
left-sided-time×levelʰ L = left-sided-intervalsʰ ×ʰ level-gradeʰ L

-- at the two-point lattice

left-sided-time×low-high : Grade ℕᴰ
left-sided-time×low-high = left-sided-time×level low-high

left-sided-time×low-highʰ : GradeHints left-sided-time×low-high
left-sided-time×low-highʰ = left-sided-time×levelʰ low-high
