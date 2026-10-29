------------------------------------------------------------------
-- Report simplification at timed traces, allowance order       --
--                                                              --
-- The unit is least, so a var-rule disjunction entailed by     --
-- another is pruned, and a product with the top among its      --
-- factors is absorbed into it.                                 --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Traces-Timed-RightSided)

module OpenCalculus.Examples.Reports.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; hints; enum)
open LanguageSpec spec using (Grades)
open GradeSystemInterface Grades using (⊤ᵣ)

open import OpenCalculus.Syntax.Grades   spec using (rconst; ∣_∣̂ᵉ; _·̂ᵣ_; _·̂ₑ_)
open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Examples.Reports spec hints enum
open import OpenCalculus.Examples.Variables

------------------------------------------------------------------
-- The disjunction owed after `f` is entailed by the one owed after
-- `f` and `g`, and only the latter is reported

reused-around-claim-reported :
  schemeOf (infer [] reused-around-claim)
    ≡ just (expected-reused-around-claim (eternal α₂ ∨ ∣ ε₁ ∣̂ᵉ ·̂ᵣ ∣ ε₀ ∣̂ᵉ ≾ûᵣ) (ε₁ ·̂ₑ ε₀))
reused-around-claim-reported = refl

------------------------------------------------------------------
-- The clause's lock, the unbounded budget, absorbs `f`'s grade:
-- the box is asked for at the top

claimed-after-call-reported :
  schemeOf (infer [] claimed-after-call) ≡ just (expected-claimed-after-call (rconst ⊤ᵣ))
claimed-after-call-reported = refl
