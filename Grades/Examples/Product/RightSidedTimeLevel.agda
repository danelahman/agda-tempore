------------------------------------------------------------------------
-- Right-sided time paired with a security level.                     --
--                                                                    --
-- A grade `([0, n ] , ℓ)` states "at most `n` time steps, touching   --
-- nothing above `ℓ`". A time step advances the first component only. --
--                                                                    --
-- As a resource grade it is an expiring, untainted capability: a     --
-- value boxed at `([0, n ] , ℓ)` can be unboxed only while at most   --
-- `n` steps have passed since boxing and nothing above `ℓ` has been  --
-- touched, as for a session token valid for `n` steps and revoked    --
-- early by reading `High` data. A variable that is not eternal goes  --
-- stale after any step or any `High` activity.                       --
--                                                                    --
-- The unit is least and `_·_` commutes; its hints declare both.      --
------------------------------------------------------------------------

module Grades.Examples.Product.RightSidedTimeLevel where

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Examples.Time.RightSided using (right-sided-intervals; right-sided-intervalsʰ)
open import Grades.Examples.SecurityLevel
  using (LevelLattice; level-grade; level-gradeʰ; low-high)

-- right-sided time and a lattice of levels

right-sided-time×level : LevelLattice → Grade ℕᴰ
right-sided-time×level L = right-sided-intervals ×ᵍ level-grade L

right-sided-time×levelʰ : (L : LevelLattice) → GradeHints (right-sided-time×level L)
right-sided-time×levelʰ L = right-sided-intervalsʰ ×ʰ level-gradeʰ L

-- at the two-point lattice

right-sided-time×low-high : Grade ℕᴰ
right-sided-time×low-high = right-sided-time×level low-high

right-sided-time×low-highʰ : GradeHints right-sided-time×low-high
right-sided-time×low-highʰ = right-sided-time×levelʰ low-high
