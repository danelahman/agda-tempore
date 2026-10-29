------------------------------------------------------------------------
-- Grade systems over left-sided time paired with a security level.   --
--                                                                    --
-- The effect grades are `([ n ,+∞⟩ , ℓ)` throughout: at least `n`    --
-- steps, nothing above `ℓ` touched. The resource grades keep both    --
-- components or one of them.                                         --
--                                                                    --
--   * Both, the projection being the identity: timed                 --
--     declassification. A report boxed at `([ 30 ,+∞⟩ , Low)` may be --
--     published once 30 steps have passed, and only from code that   --
--     has not touched `High` since boxing.                           --
--                                                                    --
--   * Time only, along `π₁ᵍ`: an embargo alone. The level is         --
--     recorded in the effect grades, so types record what code       --
--     touched, but a box does not check it.                          --
--                                                                    --
--   * The level only, along `π₂ᵍ`: a taint check alone, LIO's rule   --
--     of no write-down after read-up, with time recorded in the      --
--     effect grades but not awaited by a box.                        --
--                                                                    --
-- The identity system maps to the other two by the identity on       --
-- effect grades and the projection on resource grades, and each of   --
-- those maps to the identity system on its own component by the      --
-- projection on effect grades. The identity system is also the       --
-- product `×ˢ` of the identity systems on time and on levels. Every  --
-- square commutes up to equality.                                    --
------------------------------------------------------------------------

module Grades.Examples.System.Product.LeftSidedTimeLevel where

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Maybe.Base using (nothing)

open import Grades.Durations using (idᴰ)
open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (GradeSystem)
open import Grades.Hints using (SystemHints)
open import Grades.Product using (π₁ᵍ; π₂ᵍ; _→ˢ_; _×ˢ_⟨_⟩; _×ʰˢ_⟨_⟩; π₁ˢ)
open import Grades.Examples.System.Identity
  using (idᵍ; identityGradeSystem; identityʰ; noWitnesses)
open import Grades.Examples.Time.LeftSided using (left-sided-intervals; left-sided-intervalsʰ)
open import Grades.Examples.SecurityLevel using (two-point-levels; two-point-levelsʰ)
open import Grades.Examples.Product.LeftSidedTimeLevel
  using (left-sided-time×low-high; left-sided-time×low-highʰ)

open import Util.Equality

------------------------------------------------------------------------
-- The three systems

-- timed declassification: embargo and taint check

embargo-and-taint : GradeSystem
embargo-and-taint = identityGradeSystem left-sided-time×low-high

embargo-and-taintʰ : SystemHints embargo-and-taint
embargo-and-taintʰ = identityʰ left-sided-time×low-highʰ noWitnesses

-- embargo only

embargo : GradeSystem
embargo = record
  { Dur    = ℕᴰ
  ; RGrade = left-sided-intervals
  ; EGrade = left-sided-time×low-high
  ; ∣_∣ᵉ   = π₁ᵍ {G₁ = left-sided-intervals} {two-point-levels}
  }

embargoʰ : SystemHints embargo
embargoʰ = record
  { RHints      = left-sided-intervalsʰ
  ; EHints      = left-sided-time×low-highʰ
  ; reflects-u? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }

-- taint check only

taint : GradeSystem
taint = record
  { Dur    = ℕᴰ
  ; RGrade = two-point-levels
  ; EGrade = left-sided-time×low-high
  ; ∣_∣ᵉ   = π₂ᵍ {G₁ = left-sided-intervals} {two-point-levels}
  }

taintʰ : SystemHints taint
taintʰ = record
  { RHints      = two-point-levelsʰ
  ; EHints      = left-sided-time×low-highʰ
  ; reflects-u? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }

------------------------------------------------------------------------
-- Maps between them

embargo-and-taint→embargo : embargo-and-taint →ˢ embargo
embargo-and-taint→embargo = record
  { mapᴰ   = idᴰ
  ; mapᴱ   = idᵍ left-sided-time×low-high
  ; mapᴿ   = π₁ᵍ {G₁ = left-sided-intervals} {two-point-levels}
  ; square = λ _ → refl
  }

embargo-and-taint→taint : embargo-and-taint →ˢ taint
embargo-and-taint→taint = record
  { mapᴰ   = idᴰ
  ; mapᴱ   = idᵍ left-sided-time×low-high
  ; mapᴿ   = π₂ᵍ {G₁ = left-sided-intervals} {two-point-levels}
  ; square = λ _ → refl
  }

embargo→time : embargo →ˢ identityGradeSystem left-sided-intervals
embargo→time = record
  { mapᴰ   = idᴰ
  ; mapᴱ   = π₁ᵍ {G₁ = left-sided-intervals} {two-point-levels}
  ; mapᴿ   = idᵍ left-sided-intervals
  ; square = λ _ → refl
  }

taint→level : taint →ˢ identityGradeSystem two-point-levels
taint→level = record
  { mapᴰ   = idᴰ
  ; mapᴱ   = π₂ᵍ {G₁ = left-sided-intervals} {two-point-levels}
  ; mapᴿ   = idᵍ two-point-levels
  ; square = λ _ → refl
  }

-- the product of the two identity systems: the first system maps to it
-- by the identity on both sides, and its first projection forgets the
-- level

identities : GradeSystem
identities = identityGradeSystem left-sided-intervals
          ×ˢ identityGradeSystem two-point-levels ⟨ refl ⟩

identitiesʰ : SystemHints identities
identitiesʰ = identityʰ left-sided-intervalsʰ noWitnesses
           ×ʰˢ identityʰ two-point-levelsʰ noWitnesses ⟨ refl ⟩

embargo-and-taint→identities : embargo-and-taint →ˢ identities
embargo-and-taint→identities = record
  { mapᴰ   = idᴰ
  ; mapᴱ   = idᵍ left-sided-time×low-high
  ; mapᴿ   = idᵍ left-sided-time×low-high
  ; square = λ _ → refl
  }

identities→time : identities →ˢ identityGradeSystem left-sided-intervals
identities→time = π₁ˢ (identityGradeSystem left-sided-intervals)
                      (identityGradeSystem two-point-levels) refl

