--------------------------------------------------------------------
-- The standard library at timed traces, coverage order           --
--                                                                --
-- The unit is the top: `compose` and `min` report no time        --
-- condition.                                                     --
--------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Traces-Timed-LeftSided)

module PolymorphicCalculus.Examples.Stdlib.Traces.Timed.LeftSided where

open Traces-Timed-LeftSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Grades   spec
open import PolymorphicCalculus.Syntax.Types    spec
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Examples.Stdlib spec hints enum
open import PolymorphicCalculus.Examples.Variables

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

-- `⊤ = 𝟏` meets `f`'s disjunction

expected-compose-top : Scheme
expected-compose-top =
  ∀[ 3 , 0 , 2 ] ⊤ ⟹
    ((α₁ ⇒ α₀ ‼ ε₀) ⇒ ((α₂ ⇒ α₁ ‼ ε₁) ⇒ (α₂ ⇒ α₀ ‼ (ε₁ ·̂ₑ ε₀)) ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ

compose-reported : schemeOf (infer [] compose) ≡ just expected-compose-top
compose-reported = refl

-- `⊤ = 𝟏` meets both disjunctions; only the subtyping is left

expected-min-top : Scheme
expected-min-top =
  ∀[ 3 , 0 , 1 ] α₂ <: α₁ ∧ α₀ <: α₁ ⟹
    ((α₂ |×| α₀ ⇒ Bool ‼ ε₀) ⇒ (α₂ ⇒ (α₀ ⇒ α₁ ‼ ε₀) ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ

min-reported : schemeOf (infer [] min) ≡ just expected-min-top
min-reported = refl
