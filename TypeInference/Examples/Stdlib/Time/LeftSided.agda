-------------------------------------------------------------------
-- The standard library at left-sided intervals                  --
--                                                               --
-- "At least `n` time steps": the unit is the top, and           --
-- multiplication commutes. Nothing goes stale, so `compose` and --
-- `min` report no condition on time, and `compose` reports its  --
-- effect as a sorted product.                                   --
-------------------------------------------------------------------

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

id-reported : schemeOf (infer [] id) ≡ just expected-id
id-reported = refl

ignore-reported : schemeOf (infer [] ignore) ≡ just expected-ignore
ignore-reported = refl

fst-reported : schemeOf (infer [] fst) ≡ just expected-fst
fst-reported = refl

snd-reported : schemeOf (infer [] snd) ≡ just expected-snd
snd-reported = refl

not-reported : schemeOf (infer [] not) ≡ just expected-not
not-reported = refl

absurd′-reported : schemeOf (infer [] absurd′) ≡ just expected-absurd′
absurd′-reported = refl

pipe-reported : schemeOf (infer [] pipe) ≡ just expected-pipe
pipe-reported = refl

-- `⊤ = u`: every grade is below the unit, so the disjunction for
-- `f` is met by its grade ordering and no condition is left.
-- `·-comm?`: the product of the effects is sorted, `ε₀ ·̂ₑ ε₁`.

expected-compose-top-comm : Scheme
expected-compose-top-comm =
  ∀[ 3 , 0 , 2 ] ⊤ ⟹
    ((α₁ ⇒ α₀ ‼ ε₀) ⇒ ((α₂ ⇒ α₁ ‼ ε₁) ⇒ (α₂ ⇒ α₀ ‼ (ε₀ ·̂ₑ ε₁)) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

compose-reported : schemeOf (infer [] compose) ≡ just expected-compose-top-comm
compose-reported = refl

-- `⊤ = u`: every grade is below the unit, so both disjunctions are
-- met by their grade orderings and only the subtyping is left

expected-min-top : Scheme
expected-min-top =
  ∀[ 3 , 0 , 1 ] α₂ <: α₁ ∧ α₀ <: α₁ ⟹
    ((α₂ |×| α₀ ⇒ Bool ‼ ε₀) ⇒ (α₂ ⇒ (α₀ ⇒ α₁ ‼ ε₀) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

min-reported : schemeOf (infer [] min) ≡ just expected-min-top
min-reported = refl
