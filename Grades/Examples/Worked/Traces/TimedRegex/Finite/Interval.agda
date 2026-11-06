------------------------------------------------------------------------
-- Worked rigid timed finite-expression intervals in dense time.      --
--                                                                    --
-- An interval `[ L , U ]` pairs a lower and an upper bound that a    --
-- common run fits, checked in a literal. The lower bound demanding a --
-- wait is what separates the spans of the upper one; a delay is      --
-- graded by both hulls, a wait of exactly its length.                --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.TimedRegex.Finite.Interval where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Util.Equality

open import Grades.Examples.Time.Rational.Interval using (_/_; #_)
open import Grades.Examples.Worked.Traces.TimedRegex.Finite.Operations
open import Grades.Examples.Traces.TimedRegex.Finite.Interval Op 3 code name name-code code-name running
open import Grades.Examples.Traces.TimedRegex.Finite.Base Op 3 code name name-code code-name running
  using (Proper′; ⌜_⌝; holds; lower; upper; ε; _·_; ‵_)
import Grades.Examples.Traces.TimedRegex.Finite.LowerBound Op 3 code name name-code code-name running as L
import Grades.Examples.Traces.TimedRegex.Finite.UpperBound Op 3 code name name-code code-name running as U

open import Grades.Base using (module Grade)
open Grade interval using (Carrier; ι)
  renaming (_·_ to _·ᵢ_)

-- componentwise comparison

holds₂ : Carrier → Carrier → Bool
holds₂ ((l , u) , _) ((l′ , u′) , _) = holds l l′ ∧ holds u u′

-- heating, then a wait of at least two, then logging, all within six

bound : Carrier
bound = [ ⌜ ‵ heat · L.idle L.≥ (# 2) · ‵ log ⌝ , ⌜ ‵ heat · U.≤ (# 6) · ‵ log ⌝ ]

-- a delay of two and a half, between heating and logging, meets it

waited : Carrier
waited = operation heat ·ᵢ (ι (5 / 2) ·ᵢ operation log)

-- a delay of one and a half breaks the wait the lower bound demands

hurried : Carrier
hurried = operation heat ·ᵢ (ι (3 / 2) ·ᵢ operation log)

hurried-fails : holds₂ hurried bound ≡ false
hurried-fails = refl

waited-meets : holds₂ waited bound ≡ true
waited-meets = refl

-- a wait of at least five units within at most two: no run fits both

impatient : ¬ Consistent (⌜ L.idle L.≥ (# 5) ⌝ , ⌜ U.≤ (# 2) ⌝)
impatient = toWitnessFalse {a? = consistent? (⌜ L.idle L.≥ (# 5) ⌝ , ⌜ U.≤ (# 2) ⌝)} _
