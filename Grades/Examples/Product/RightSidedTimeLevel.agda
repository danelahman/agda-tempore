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
-- The unit is least and `_·_` commutes; both are declared.           --
------------------------------------------------------------------------

module Grades.Examples.Product.RightSidedTimeLevel where

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Product using (_×ᵍ_)
open import Grades.Examples.Time.RightSided using (right-sided-intervals)
open import Grades.Examples.SecurityLevel
  using (LevelLattice; level-grade; low-high)

-- right-sided time and a lattice of levels

right-sided-time×level : LevelLattice → Grade ℕᴰ
right-sided-time×level L = right-sided-intervals ×ᵍ level-grade L

-- at the two-point lattice

right-sided-time×low-high : Grade ℕᴰ
right-sided-time×low-high = right-sided-time×level low-high
