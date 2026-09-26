------------------------------------------------------------------------
-- Left-sided time paired with a security level.                        --
--                                                                     --
-- A grade `([ n ,+∞⟩ , ℓ)` says "at least `n` time steps, touching     --
-- nothing above `ℓ`". A time step advances the first component only.   --
--                                                                     --
-- As a resource grade it reads as an embargo with a taint check: a     --
-- value boxed at `([ n ,+∞⟩ , ℓ)` can be unboxed once at least `n`     --
-- steps have passed since boxing, and only while nothing above `ℓ` has --
-- been touched since -- a report publishable after the embargo, and    --
-- only from untainted code. The left-sided unit is greatest, so time   --
-- alone never makes a variable stale; touching `High` does.            --
--                                                                     --
-- The unit is not least, as for left-sided time; `_·_` commutes.       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Product.LeftSidedTimeLevel where

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)
open import Syntax.Grades.Example.Time.LeftSided using (left-sided-intervals)
open import Syntax.Grades.Example.SecurityLevel
  using (LevelLattice; level-grade; low-high)

-- left-sided time and a lattice of levels

left-sided-time×level : LevelLattice → Grade
left-sided-time×level L = left-sided-intervals ×ᵍ level-grade L

-- at the two-point lattice

left-sided-time×low-high : Grade
left-sided-time×low-high = left-sided-time×level low-high
