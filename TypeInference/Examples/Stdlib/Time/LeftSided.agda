------------------------------------------------------------------
-- The standard library at left-sided intervals                   --
--                                                                --
-- "At least `n` time steps": the unit is the top, and            --
-- multiplication commutes. Nothing goes stale, so `compose` and  --
-- `min` report no condition on time, and `compose` reports its   --
-- effect as a sorted product.                                    --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-LeftSided)

module TypeInference.Examples.Stdlib.Time.LeftSided where

open Time-LeftSided using (spec; enum)

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Examples.Stdlib     spec enum
open import TypeInference.Examples.Variables

id-reported : report (infer [] id) ≡ just expected-id
id-reported = refl

ignore-reported : report (infer [] ignore) ≡ just expected-ignore
ignore-reported = refl

fst-reported : report (infer [] fst) ≡ just expected-fst
fst-reported = refl

snd-reported : report (infer [] snd) ≡ just expected-snd
snd-reported = refl

not-reported : report (infer [] not) ≡ just expected-not
not-reported = refl

absurd′-reported : report (infer [] absurd′) ≡ just expected-absurd′
absurd′-reported = refl

pipe-reported : report (infer [] pipe) ≡ just expected-pipe
pipe-reported = refl

-- `⊤ = u`: every grade is below the unit, so the disjunction for
-- `f` is met by its grade ordering and no condition is left.
-- `·-comm?`: the product of the effects is sorted, `ε₀ ·̂ₑ ε₁`.

expected-compose-top-comm : Report
expected-compose-top-comm =
  ∀[ 3 , 0 , 2 ] ⊤ ⟹
    ((α₁ ⇒ α₀ ‼ ε₀) ⇒ ((α₂ ⇒ α₁ ‼ ε₁) ⇒ (α₂ ⇒ α₀ ‼ (ε₀ ·̂ₑ ε₁)) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

compose-reported : report (infer [] compose) ≡ just expected-compose-top-comm
compose-reported = refl

-- `⊤ = u`: every grade is below the unit, so both disjunctions are
-- met by their grade orderings and only the subtyping is left

expected-min-top : Report
expected-min-top =
  ∀[ 3 , 0 , 1 ] α₀ <: α₁ ∧ α₂ <: α₁ ⟹
    ((α₂ |×| α₀ ⇒ Bool ‼ ε₀) ⇒ (α₂ ⇒ (α₀ ⇒ α₁ ‼ ε₀) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

min-reported : report (infer [] min) ≡ just expected-min-top
min-reported = refl
