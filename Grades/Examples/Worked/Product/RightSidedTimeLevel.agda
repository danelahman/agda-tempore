------------------------------------------------------------------------
-- Worked instances of right-sided time paired with a security level. --
--                                                                    --
-- The expiring-untainted-capability grade `([0, n ] , ℓ)` at the     --
-- sensor node, each operation graded by `slow` and `touches`:        --
-- orderings and sequencing, established by the decision procedure of --
-- the grade or by computation.                                       --
------------------------------------------------------------------------

module Grades.Examples.Worked.Product.RightSidedTimeLevel where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)
open import Grades.Examples.Time.RightSided using ([0,_]; ↑_; ∞)
open import Grades.Examples.SecurityLevel using (Low; High)
open import Grades.Examples.Product.RightSidedTimeLevel
  using (right-sided-time×low-high)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; slow)
open import Grades.Examples.Worked.Operations.Footprint using (touches)

open import Util.Equality

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade right-sided-time×low-high

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- an operation of the sensor node: the time it may take at worst, and
-- the level it touches

node : Op → Carrier
node o = ([0, ↑ slow o ] , touches o)

-- the token's box: valid for 10 steps of untainted work

token : Carrier
token = ([0, ↑ 10 ] , Low)

-- `logged`: four steps at worst, all `Low`, and the token is still
-- valid

in-time : node read · node write ≾ token
in-time = ≾! (node read · node write) token

-- `logged` and eight ticks of idling: twelve steps, expired

expired : ¬ (node read · node write · of-dur 8 ≾ token)
expired = ⋠! (node read · node write · of-dur 8) token

-- `uplink`: nine steps, in time, but it transmits, and the token is
-- revoked

revoked : ¬ (node read · of-dur 2 · node send ≾ token)
revoked = ⋠! (node read · of-dur 2 · node send) token

-- the unit, no time and nothing touched, is below everything

unit-below : u ≾ ([0, ↑ 0 ] , High)
unit-below = ≾! u ([0, ↑ 0 ] , High)

-- sequencing adds the time and joins the levels

seq : of-dur 2 · node send ≡ ([0, ↑ 8 ] , High)
seq = refl

-- the greatest grade: no deadline, anything touched

top : ⊤ ≡ ([0, ∞ ] , High)
top = refl
