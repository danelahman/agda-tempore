------------------------------------------------------------------------
-- Programs at upper bounds                                           --
--                                                                    --
-- The scheme of `keep` requires an eternal type, so `keep-twice` is  --
-- accepted and `keep-late`, keeping a function, is rejected at       --
-- `late`.                                                            --
------------------------------------------------------------------------

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just)

open import Grades.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-UpperBound)

module PolymorphicCalculus.Examples.Programs.Time.UpperBound where

open Time-UpperBound using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Types spec
open import PolymorphicCalculus.Examples.Programs spec hints enum ℕᴰ-stepped
open import PolymorphicCalculus.Examples.Variables

keep-twice-reported :
  schemesOf (checkProgram keep-twice)
    ≡ just ( (∀ᵛ[ 1 , 0 , 0 ] eternal α₀ ⟹ α₀ ⇒ α₀ ! ⌜ 1 ⌝ᵉ)
           ∷ (∀ᵛ[ 1 , 0 , 0 ] ⊤ ⟹ α₀ ⇒ bool ! ⌜ 2 ⌝ᵉ)
           ∷ [])
keep-twice-reported = refl

keep-late-rejected : rejectedAt (checkProgram keep-late) ≡ just 1
keep-late-rejected = refl
