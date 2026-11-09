------------------------------------------------------------------------
-- Upper bounds on time paired with a lattice.                        --
--                                                                    --
-- A grade `([0, n ] , ℓ)` states "at most `n` time steps, touching   --
-- nothing above `ℓ`". A time step advances the first component only. --
--                                                                    --
-- As a resource grade it is an expiring, untainted capability: a     --
-- value boxed at `([0, n ] , ℓ)` can be unboxed only while at most   --
-- `n` steps have passed since boxing and nothing above `ℓ` has been  --
-- touched, as for a session token valid for `n` steps and revoked    --
-- early by reading `High` data. A variable that is noneternal goes   --
-- stale after any step or any `High` activity.                       --
--                                                                    --
-- The unit is least, `_·_` commutes and every grade has a closure;   --
-- its hints declare all three.                                       --
------------------------------------------------------------------------

module Grades.Examples.Product.TimeUpperBoundLattice where

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Examples.Time.UpperBound using (upper-bound; upper-boundʰ)
open import Grades.Examples.Lattice
  using (LevelLattice; level-grade; level-gradeʰ; low-high-lattice)

-- upper bounds on time and a lattice of levels

time-upper-bound×lattice : LevelLattice → Grade ℕᴰ
time-upper-bound×lattice L = upper-bound ×ᵍ level-grade L

time-upper-bound×latticeʰ : (L : LevelLattice) → GradeHints (time-upper-bound×lattice L)
time-upper-bound×latticeʰ L = upper-boundʰ ×ʰ level-gradeʰ L

-- at the two-point lattice

time-upper-bound×low-high : Grade ℕᴰ
time-upper-bound×low-high = time-upper-bound×lattice low-high-lattice

time-upper-bound×low-highʰ : GradeHints time-upper-bound×low-high
time-upper-bound×low-highʰ = time-upper-bound×latticeʰ low-high-lattice
