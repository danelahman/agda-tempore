--------------------------------------------------------------------
-- The standard library at right-sided intervals                  --
--                                                                --
-- "At most `n` time steps": the unit is least and multiplication --
-- commutes. `compose` reports its effect as a sorted product.    --
--------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-RightSided)

module TypeInference.Examples.Stdlib.Time.RightSided where

open Time-RightSided using (spec; enum)

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

-- `·-comm?`: the product of the effects is sorted, `ε₀ ·̂ₑ ε₁`

expected-compose-comm : Scheme
expected-compose-comm =
  ∀[ 3 , 0 , 2 ] ∣ ε₁ ∣̂ᵉ ≾ᵣ ûᵣ ⟹
    ((α₁ ⇒ α₀ ‼ ε₀) ⇒ ((α₂ ⇒ α₁ ‼ ε₁) ⇒ (α₂ ⇒ α₀ ‼ (ε₀ ·̂ₑ ε₁)) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

compose-reported : schemeOf (infer [] compose) ≡ just expected-compose-comm
compose-reported = refl

min-reported : schemeOf (infer [] min) ≡ just expected-min
min-reported = refl
