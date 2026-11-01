------------------------------------------------------------------------
-- Report simplification at right-sided intervals                     --
--                                                                    --
-- The unit is least, so both simplifications apply.                  --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-RightSided)

module PolymorphicCalculus.Examples.Reports.Time.RightSided where

open Time-RightSided using (spec; hints; enum)
open LanguageSpec spec using (Grades)
open GradeSystemInterface Grades using (⊤ᵣ)

open import PolymorphicCalculus.Syntax.Grades   spec using (rconst; ∣_∣̂ᵉ; _·̂ᵣ_; _·̂ₑ_)
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Examples.Reports spec hints enum
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- Only the disjunction owed after `f` and `g` is reported

reused-around-claim-reported :
  schemeOf (infer [] reused-around-claim)
    ≡ just (expected-reused-around-claim (eternal α₂ ∨ ∣ ε₀ ∣̂ᵉ ·̂ᵣ ∣ ε₁ ∣̂ᵉ ≾𝟏̂ᵣ) (ε₀ ·̂ₑ ε₁))
reused-around-claim-reported = refl

------------------------------------------------------------------
-- The box is asked for at the top

claimed-after-call-reported :
  schemeOf (infer [] claimed-after-call) ≡ just (expected-claimed-after-call (rconst ⊤ᵣ))
claimed-after-call-reported = refl
