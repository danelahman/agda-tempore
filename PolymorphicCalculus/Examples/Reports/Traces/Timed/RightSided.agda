------------------------------------------------------------------
-- Report simplification at timed traces, allowance order       --
--                                                              --
-- Both simplifications apply, the unit being least.            --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Traces-Timed-RightSided)

module PolymorphicCalculus.Examples.Reports.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; hints; enum)
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
    ≡ just (expected-reused-around-claim (eternal α₂ ∨ ∣ ε₁ ∣̂ᵉ ·̂ᵣ ∣ ε₀ ∣̂ᵉ ≾𝟏̂ᵣ) (ε₁ ·̂ₑ ε₀))
reused-around-claim-reported = refl

------------------------------------------------------------------
-- The box is asked for at the top

claimed-after-call-reported :
  schemeOf (infer [] claimed-after-call) ≡ just (expected-claimed-after-call (rconst ⊤ᵣ))
claimed-after-call-reported = refl
