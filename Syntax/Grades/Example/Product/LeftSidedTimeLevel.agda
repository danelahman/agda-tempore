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

open import Data.Maybe.Base using (nothing)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)
open import Syntax.Grades.Example.Time.LeftSided
  using ([_,+∞⟩; left-sided-intervals)
open import Syntax.Grades.Example.SecurityLevel
  using (LevelLattice; level-grade; low-high; LowHigh; Low; High)

open import Util.Equality

-- left-sided time and a lattice of levels

left-sided-time×level : LevelLattice → Grade
left-sided-time×level L = left-sided-intervals ×ᵍ level-grade L

-- at the two-point lattice

left-sided-time×low-high : Grade
left-sided-time×low-high = left-sided-time×level low-high

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade left-sided-time×low-high

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- the report's box: publishable after 30 steps, from untainted code

report : Carrier
report = ([ 30 ,+∞⟩ , Low)

-- 45 steps of `Low` work: the embargo is over

after-embargo : ([ 45 ,+∞⟩ , Low) ≾ report
after-embargo = ≾! ([ 45 ,+∞⟩ , Low) report

-- 20 steps: still under embargo

under-embargo : ¬ (([ 20 ,+∞⟩ , Low) ≾ report)
under-embargo = ⋠! ([ 20 ,+∞⟩ , Low) report

-- 45 steps that read `High` data: tainted

tainted : ¬ (([ 45 ,+∞⟩ , High) ≾ report)
tainted = ⋠! ([ 45 ,+∞⟩ , High) report

-- waiting advances time and leaves the level alone

wait : of-nat 20 ≡ ([ 20 ,+∞⟩ , Low)
wait = refl

-- sequencing adds the time and joins the levels

seq : of-nat 20 · ([ 1 ,+∞⟩ , High) ≡ ([ 21 ,+∞⟩ , High)
seq = refl

-- the join keeps the smaller guarantee and the higher level

join : ([ 10 ,+∞⟩ , Low) ⊔ ([ 20 ,+∞⟩ , High) ≡ ([ 10 ,+∞⟩ , High)
join = refl

-- the unit is not declared least

unit-not-least : u-least? ≡ nothing
unit-not-least = refl
