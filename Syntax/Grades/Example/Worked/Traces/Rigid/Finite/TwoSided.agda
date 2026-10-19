------------------------------------------------------------------------
-- Worked rigid timed finite-expression intervals in dense time.      --
--                                                                    --
-- An interval `[ L , U ]` pairs a lower and an upper bound. The      --
-- lower bound demanding a wait is what separates the budgets of the  --
-- upper one; a delay is graded by both hulls, a wait of exactly its  --
-- length.                                                            --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Finite.TwoSided where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Util.Equality

open import Syntax.Grades.Example.Time.Dense.TwoSided using (_/_; #_)
open import Syntax.Grades.Example.Worked.Traces.Rigid.Finite.Operations
open import Syntax.Grades.Example.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
open import Syntax.Grades.Example.Traces.Rigid.Finite.Base Op 3 code name name-code code-name running
  using (Proper′; ⌜_⌝; holds; waitᴸ; waitᵁ; lower; upper; ε; _·_; ‵_; _·ᵉ_)
import Syntax.Grades.Example.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running as L
import Syntax.Grades.Example.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running as U

-- componentwise comparison

holds₂ : Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper → Bool
holds₂ (l , u) (l′ , u′) = holds l l′ ∧ holds u u′

-- heating, then a wait of at least two, then logging, all within six

bound : Proper′ lower × Proper′ upper
bound = [ ⌜ ‵ heat · L.!≥ (# 2) · ‵ log ⌝ , ⌜ ‵ heat · U.≤ (# 6) · ‵ log ⌝ ]

-- a delay of two and a half, between heating and logging, meets it

waited : Proper′ lower × Proper′ upper
waited = [ ⌜ ‵ heat ⌝ , ⌜ ‵ heat ⌝ ] ·₂ ((waitᴸ (5 / 2) , waitᵁ (5 / 2)) ·₂ [ ⌜ ‵ log ⌝ , ⌜ ‵ log ⌝ ])
  where
    _·₂_ : Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper
    (l , u) ·₂ (l′ , u′) = (l ·ᵉ l′) , (u ·ᵉ u′)

-- a delay of one and a half breaks the wait the lower bound demands

hurried : Proper′ lower × Proper′ upper
hurried = [ ⌜ ‵ heat ⌝ , ⌜ ‵ heat ⌝ ] ·₂ ((waitᴸ (3 / 2) , waitᵁ (3 / 2)) ·₂ [ ⌜ ‵ log ⌝ , ⌜ ‵ log ⌝ ])
  where
    _·₂_ : Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper
    (l , u) ·₂ (l′ , u′) = (l ·ᵉ l′) , (u ·ᵉ u′)

hurried-fails : holds₂ hurried bound ≡ false
hurried-fails = refl

waited-meets : holds₂ waited bound ≡ true
waited-meets = refl
