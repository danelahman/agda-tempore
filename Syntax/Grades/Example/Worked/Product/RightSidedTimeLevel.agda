------------------------------------------------------------------------
-- Worked instances of right-sided time paired with a security level.  --
--                                                                     --
-- The expiring-untainted-capability grade `([0, n ] , ℓ)`: orderings   --
-- and sequencing, checked by the grade's own decision procedure or by  --
-- computation.                                                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Product.RightSidedTimeLevel where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Example.Time.RightSided using ([0,_]; ↑_; ∞)
open import Syntax.Grades.Example.SecurityLevel using (Low; High)
open import Syntax.Grades.Example.Product.RightSidedTimeLevel
  using (right-sided-time×low-high)

open import Util.Equality

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
