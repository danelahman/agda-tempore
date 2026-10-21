------------------------------------------------------------------------
-- Worked rigid timed finite-expression intervals in dense time.      --
--                                                                    --
-- An interval `[ L , U ]` pairs a lower and an upper bound that a    --
-- common run fits, checked in a literal. The lower bound demanding a --
-- wait is what separates the budgets of the upper one; a delay is    --
-- graded by both hulls, a wait of exactly its length.                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Finite.TwoSided where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Util.Equality

open import Syntax.Grades.Example.Time.Dense.TwoSided using (_/_; #_)
open import Syntax.Grades.Example.Worked.Traces.Rigid.Finite.Operations
open import Syntax.Grades.Example.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
open import Syntax.Grades.Example.Traces.Rigid.Finite.Base Op 3 code name name-code code-name running
  using (Proper′; ⌜_⌝; holds; lower; upper; ε; _·_; ‵_)
import Syntax.Grades.Example.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running as L
import Syntax.Grades.Example.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running as U

open import Syntax.Grades using (module Grade)
open Grade two-sided using (Carrier; of-dur)
  renaming (_·_ to _·ᵢ_)

-- componentwise comparison

holds₂ : Carrier → Carrier → Bool
holds₂ ((l , u) , _) ((l′ , u′) , _) = holds l l′ ∧ holds u u′

-- heating, then a wait of at least two, then logging, all within six

bound : Carrier
bound = [ ⌜ ‵ heat · L.!≥ (# 2) · ‵ log ⌝ , ⌜ ‵ heat · U.≤ (# 6) · ‵ log ⌝ ]

-- a delay of two and a half, between heating and logging, meets it

waited : Carrier
waited = operation heat ·ᵢ (of-dur (5 / 2) ·ᵢ operation log)

-- a delay of one and a half breaks the wait the lower bound demands

hurried : Carrier
hurried = operation heat ·ᵢ (of-dur (3 / 2) ·ᵢ operation log)

hurried-fails : holds₂ hurried bound ≡ false
hurried-fails = refl

waited-meets : holds₂ waited bound ≡ true
waited-meets = refl

-- a wait of at least five units within at most two: no run fits both

impatient : ¬ Consistent (⌜ L.!≥ (# 5) ⌝ , ⌜ U.≤ (# 2) ⌝)
impatient = toWitnessFalse {a? = consistent? (⌜ L.!≥ (# 5) ⌝ , ⌜ U.≤ (# 2) ⌝)} _
