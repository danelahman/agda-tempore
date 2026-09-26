------------------------------------------------------------------------
-- Right-sided time paired with a security level.                       --
--                                                                     --
-- A grade `([0, n ] , ℓ)` says "at most `n` time steps, touching       --
-- nothing above `ℓ`". A time step advances the first component only.   --
--                                                                     --
-- As a resource grade it reads as an expiring, untainted capability: a --
-- value boxed at `([0, n ] , ℓ)` can be unboxed only while at most `n` --
-- steps have passed since boxing and nothing above `ℓ` has been        --
-- touched -- a session token valid for `n` steps, revoked early by     --
-- reading `High` data. A variable that is not eternal goes stale after --
-- any step or any `High` activity.                                     --
--                                                                     --
-- The unit is least and `_·_` commutes; both are declared.             --
------------------------------------------------------------------------

module Syntax.Grades.Example.Product.RightSidedTimeLevel where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)
open import Syntax.Grades.Example.Time.RightSided
  using ([0,_]; ↑_; ∞; right-sided-intervals)
open import Syntax.Grades.Example.SecurityLevel
  using (LevelLattice; level-grade; low-high; LowHigh; Low; High)

open import Util.Equality

-- right-sided time and a lattice of levels

right-sided-time×level : LevelLattice → Grade
right-sided-time×level L = right-sided-intervals ×ᵍ level-grade L

-- at the two-point lattice

right-sided-time×low-high : Grade
right-sided-time×low-high = right-sided-time×level low-high

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade right-sided-time×low-high

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- the token's box: valid for 10 steps of untainted work

token : Carrier
token = ([0, ↑ 10 ] , Low)

-- 6 steps of `Low` work: still valid

in-time : ([0, ↑ 6 ] , Low) ≾ token
in-time = ≾! ([0, ↑ 6 ] , Low) token

-- 12 steps: expired

expired : ¬ (([0, ↑ 12 ] , Low) ≾ token)
expired = ⋠! ([0, ↑ 12 ] , Low) token

-- 6 steps that read `High` data: revoked

revoked : ¬ (([0, ↑ 6 ] , High) ≾ token)
revoked = ⋠! ([0, ↑ 6 ] , High) token

-- the unit, no time and nothing touched, is below everything

unit-below : u ≾ ([0, ↑ 0 ] , High)
unit-below = ≾! u ([0, ↑ 0 ] , High)

-- sequencing adds the time and joins the levels

seq : of-nat 4 · ([0, ↑ 2 ] , High) ≡ ([0, ↑ 6 ] , High)
seq = refl

-- the greatest grade: no deadline, anything touched

top : ⊤ ≡ ([0, ∞ ] , High)
top = refl
