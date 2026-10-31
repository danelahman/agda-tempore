------------------------------------------------------------------------
-- Worked rigid timed regular-expression intervals in dense time.     --
--                                                                    --
-- An interval `[ L , U ]` pairs a lower and an upper bound that a    --
-- common run fits, checked in a literal. Here a cycle: heating, then --
-- a rest of at least one unit and at most three, repeated at least   --
-- once. Delays are graded by both hulls, a wait of exactly their     --
-- length.                                                            --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.Rigid.Rational.TwoSided where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Util.Equality

open import Grades.Examples.Time.Dense.TwoSided using (_/_; #_)
open import Grades.Examples.Worked.Traces.Rigid.Finite.Operations
open import Grades.Examples.Traces.Rigid.Rational.TwoSided Op 3 code name name-code code-name running
open import Grades.Examples.Traces.Rigid.Rational.Base Op 3 code name name-code code-name running
  using (⌜_⌝; holds; _·_; ‵_; _⁺ᵉ)
import Grades.Examples.Traces.Rigid.Rational.LeftSided Op 3 code name name-code code-name running as L
import Grades.Examples.Traces.Rigid.Rational.RightSided Op 3 code name name-code code-name running as U

open import Grades.Base using (module Grade)
open Grade two-sided using (Carrier; ι)
  renaming (_·_ to _·ᵢ_)

-- componentwise comparison

holds₂ : Carrier → Carrier → Bool
holds₂ ((l , u) , _) ((l′ , u′) , _) = holds l l′ ∧ holds u u′

-- heating, then a rest of between one and three units, at least once;
-- one cycle with a rest of one unit is a common run

cycle : Carrier
cycle = [ ⌜ ‵ heat · L.idle L.≥ (# 1) ⌝ ⁺ᵉ , ⌜ ‵ heat · U.idle U.≤ (# 3) ⌝ ⁺ᵉ ]

-- two cycles with rests of one and a half and of two meet it

twice : holds₂ (operation heat ·ᵢ (ι (3 / 2) ·ᵢ (operation heat ·ᵢ ι (# 2)))) cycle ≡ true
twice = refl

-- a rest of half a unit is too short, one of four too long

hurried : holds₂ (operation heat ·ᵢ ι (1 / 2)) cycle ≡ false
hurried = refl

dawdling : holds₂ (operation heat ·ᵢ ι (# 4)) cycle ≡ false
dawdling = refl

-- a wait of at least five units within at most two: no run fits both

impatient : ¬ Consistent (⌜ L.idle L.≥ (# 5) ⌝ , ⌜ U.≤ (# 2) ⌝)
impatient = toWitnessFalse {a? = consistent? (⌜ L.idle L.≥ (# 5) ⌝ , ⌜ U.≤ (# 2) ⌝)} _
