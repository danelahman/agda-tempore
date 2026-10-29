------------------------------------------------------------------
-- Programs at right-sided intervals                            --
--                                                              --
-- "At most `n` ticks": a variable used after a tick has to be  --
-- eternal, so `keep`'s scheme requires its type to be. `twice` --
-- uses `keep` at `unit` and at `bool`, both eternal; `late`,   --
-- keeping a function, is rejected.                             --
------------------------------------------------------------------

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just)

open import Grades.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Time-RightSided)

module OpenCalculus.Examples.Programs.Time.RightSided where

open Time-RightSided using (spec; hints; enum)

open import OpenCalculus.Syntax.Types spec
open import OpenCalculus.Examples.Programs spec hints enum ℕᴰ-stepped
open import OpenCalculus.Examples.Variables

keep-twice-reported :
  schemesOf (checkProgram keep-twice)
    ≡ just ( (∀ᵛ[ 1 , 0 , 0 ] eternal α₀ ⟹ α₀ ⇒ α₀ ‼ ⌜ 1 ⌝ᵉ)
           ∷ (∀ᵛ[ 1 , 0 , 0 ] ⊤ ⟹ α₀ ⇒ Bool ‼ ⌜ 2 ⌝ᵉ)
           ∷ [])
keep-twice-reported = refl

keep-late-rejected : rejectedAt (checkProgram keep-late) ≡ just 1
keep-late-rejected = refl
