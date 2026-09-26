------------------------------------------------------------------
-- Report simplification at timed traces, allowance order         --
--                                                                --
-- The unit is least, so a var-rule disjunction entailed by       --
-- another is pruned, and a product with the top among its        --
-- factors is absorbed into it.                                   --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Examples.Specs using (module Traces-Timed-RightSided)

module TypeInference.Examples.Reports.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; enum)
open LanguageSpec spec using (Grades)
open GradeSystemInterface Grades using (⊤ᵣ)

open import TypeInference.OpenSyntax.Grades   spec using (rconst; ∣_∣̂ᵉ; _·̂ᵣ_; _·̂ₑ_)
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Examples.Reports spec enum
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- The disjunction owed after `f` is entailed by the one owed after
-- `f` and `g`, and only the latter is reported

reused-around-claim-reported :
  report (infer [] reused-around-claim)
    ≡ just (expected-reused-around-claim (eternal α₂ ∨ ∣ ε₁ ∣̂ᵉ ·̂ᵣ ∣ ε₀ ∣̂ᵉ ≾ûᵣ) (ε₁ ·̂ₑ ε₀))
reused-around-claim-reported = refl

------------------------------------------------------------------
-- The clause's lock, the unbounded budget, absorbs `f`'s grade:
-- the box is asked for at the top

claimed-after-call-reported :
  report (infer [] claimed-after-call) ≡ just (expected-claimed-after-call (rconst ⊤ᵣ))
claimed-after-call-reported = refl
