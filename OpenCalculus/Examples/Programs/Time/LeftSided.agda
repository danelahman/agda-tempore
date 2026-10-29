------------------------------------------------------------------
-- Programs at left-sided intervals                             --
--                                                              --
-- "At least `n` ticks": nothing goes stale, so `keep`'s scheme --
-- has no hypothesis, and `late`, keeping a function, is        --
-- accepted.                                                    --
------------------------------------------------------------------

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just)

open import Grades.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Time-LeftSided)

module OpenCalculus.Examples.Programs.Time.LeftSided where

open Time-LeftSided using (spec; hints; enum)

open import OpenCalculus.Syntax.Grades spec using (ûₑ)
open import OpenCalculus.Syntax.Types spec
open import OpenCalculus.Examples.Programs spec hints enum ℕᴰ-stepped
open import OpenCalculus.Examples.Variables

keep-twice-reported :
  schemesOf (checkProgram keep-twice)
    ≡ just ( (∀ᵛ[ 1 , 0 , 0 ] ⊤ ⟹ α₀ ⇒ α₀ ‼ ⌜ 1 ⌝ᵉ)
           ∷ (∀ᵛ[ 1 , 0 , 0 ] ⊤ ⟹ α₀ ⇒ Bool ‼ ⌜ 2 ⌝ᵉ)
           ∷ [])
keep-twice-reported = refl

keep-late-reported :
  schemesOf (checkProgram keep-late)
    ≡ just ( (∀ᵛ[ 1 , 0 , 0 ] ⊤ ⟹ α₀ ⇒ α₀ ‼ ⌜ 1 ⌝ᵉ)
           ∷ (∀ᵛ[ 2 , 0 , 0 ] ⊤ ⟹ α₁ ⇒ (α₀ ⇒ α₀ ‼ ûₑ) ‼ ⌜ 1 ⌝ᵉ)
           ∷ [])
keep-late-reported = refl
