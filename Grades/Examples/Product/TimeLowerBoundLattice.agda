------------------------------------------------------------------------
-- Lower bounds on time paired with a lattice.                        --
--                                                                    --
-- A grade `([ n ,+∞⟩ , ℓ)` states "at least `n` time steps, touching --
-- nothing above `ℓ`". A time step advances the first component only. --
--                                                                    --
-- As a resource grade it is an embargo with a taint check: a value   --
-- boxed at `([ n ,+∞⟩ , ℓ)` can be unboxed once at least `n` steps   --
-- have passed since boxing, and only while nothing above `ℓ` has     --
-- been touched since, as for a report that may be published after an --
-- embargo and only from untainted code. The lower-bound unit is      --
-- greatest, so time alone never makes a variable stale; touching     --
-- `High` does.                                                       --
--                                                                    --
-- The unit is not least, as for lower bounds on time; `_·_`          --
-- commutes and every grade has a closure, as its hints declare.      --
------------------------------------------------------------------------

module Grades.Examples.Product.TimeLowerBoundLattice where

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Examples.Time.LowerBound using (lower-bound; lower-boundʰ)
open import Grades.Examples.Lattice
  using (LevelLattice; level-grade; level-gradeʰ; low-high-lattice)

-- lower bounds on time and a lattice of levels

time-lower-bound×lattice : LevelLattice → Grade ℕᴰ
time-lower-bound×lattice L = lower-bound ×ᵍ level-grade L

time-lower-bound×latticeʰ : (L : LevelLattice) → GradeHints (time-lower-bound×lattice L)
time-lower-bound×latticeʰ L = lower-boundʰ ×ʰ level-gradeʰ L

-- at the two-point lattice

time-lower-bound×low-high : Grade ℕᴰ
time-lower-bound×low-high = time-lower-bound×lattice low-high-lattice

time-lower-bound×low-highʰ : GradeHints time-lower-bound×low-high
time-lower-bound×low-highʰ = time-lower-bound×latticeʰ low-high-lattice
