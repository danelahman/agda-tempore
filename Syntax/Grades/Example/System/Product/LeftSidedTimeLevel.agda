------------------------------------------------------------------------
-- Grade systems over left-sided time paired with a security level.     --
--                                                                     --
-- The effect grades are `([ n ,+∞⟩ , ℓ)` throughout: at least `n`      --
-- steps, nothing above `ℓ` touched. The resource grades keep both      --
-- components or one of them.                                           --
--                                                                     --
--   * both, the projection the identity: timed declassification. A     --
--     report boxed at `([ 30 ,+∞⟩ , Low)` is publishable once 30 steps --
--     have passed, and only from code that has not touched `High`      --
--     since boxing.                                                    --
--                                                                     --
--   * time only, along `π₁ᵍ`: an embargo alone. The level is still     --
--     recorded in effect grades, so types still say what code touched, --
--     but a box no longer checks it.                                   --
--                                                                     --
--   * the level only, along `π₂ᵍ`: a taint check alone, LIO's no       --
--     write-down after read-up, with time recorded in effect grades    --
--     but never awaited by a box.                                      --
--                                                                     --
-- The identity system maps to the other two by the identity on effect  --
-- grades and the projection on resource grades, and each of those maps --
-- to the identity system on its own component by the projection on     --
-- effect grades. The identity system is also the product `×ˢ` of the   --
-- identity systems on time and on levels. Every square commutes on the --
-- nose.                                                                --
------------------------------------------------------------------------

module Syntax.Grades.Example.System.Product.LeftSidedTimeLevel where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade; GradeSystem; _→ᵍ_)
open import Syntax.Grades.Product using (π₁ᵍ; π₂ᵍ; _→ˢ_; _×ˢ_; π₁ˢ)
open import Syntax.Grades.Example.System.Identity
  using (idᵍ; identityGradeSystem)
open import Syntax.Grades.Example.Time.LeftSided
  using (𝕀; [_,+∞⟩; left-sided-intervals)
open import Syntax.Grades.Example.SecurityLevel
  using (LowHigh; Low; High; two-point-levels)
open import Syntax.Grades.Example.Product.LeftSidedTimeLevel
  using (left-sided-time×low-high)

open import Util.Equality

------------------------------------------------------------------------
-- The three systems

-- timed declassification: embargo and taint check

embargo-and-taint : GradeSystem
embargo-and-taint = identityGradeSystem left-sided-time×low-high

-- embargo only

embargo : GradeSystem
embargo = record
  { RGrade = left-sided-intervals
  ; EGrade = left-sided-time×low-high
  ; ∣_∣ᵉ   = π₁ᵍ {left-sided-intervals} {two-point-levels}
  }

-- taint check only

taint : GradeSystem
taint = record
  { RGrade = two-point-levels
  ; EGrade = left-sided-time×low-high
  ; ∣_∣ᵉ   = π₂ᵍ {left-sided-intervals} {two-point-levels}
  }

------------------------------------------------------------------------
-- Maps between them

embargo-and-taint→embargo : embargo-and-taint →ˢ embargo
embargo-and-taint→embargo = record
  { mapᴱ   = idᵍ left-sided-time×low-high
  ; mapᴿ   = π₁ᵍ {left-sided-intervals} {two-point-levels}
  ; square = λ _ → refl
  }

embargo-and-taint→taint : embargo-and-taint →ˢ taint
embargo-and-taint→taint = record
  { mapᴱ   = idᵍ left-sided-time×low-high
  ; mapᴿ   = π₂ᵍ {left-sided-intervals} {two-point-levels}
  ; square = λ _ → refl
  }

embargo→time : embargo →ˢ identityGradeSystem left-sided-intervals
embargo→time = record
  { mapᴱ   = π₁ᵍ {left-sided-intervals} {two-point-levels}
  ; mapᴿ   = idᵍ left-sided-intervals
  ; square = λ _ → refl
  }

taint→level : taint →ˢ identityGradeSystem two-point-levels
taint→level = record
  { mapᴱ   = π₂ᵍ {left-sided-intervals} {two-point-levels}
  ; mapᴿ   = idᵍ two-point-levels
  ; square = λ _ → refl
  }

-- the product of the two identity systems: the first system maps to it
-- by the identity on both sides, and its first projection forgets the
-- level

identities : GradeSystem
identities = identityGradeSystem left-sided-intervals
          ×ˢ identityGradeSystem two-point-levels

embargo-and-taint→identities : embargo-and-taint →ˢ identities
embargo-and-taint→identities = record
  { mapᴱ   = idᵍ left-sided-time×low-high
  ; mapᴿ   = idᵍ left-sided-time×low-high
  ; square = λ _ → refl
  }

identities→time : identities →ˢ identityGradeSystem left-sided-intervals
identities→time = π₁ˢ {identityGradeSystem left-sided-intervals}
                      {identityGradeSystem two-point-levels}

------------------------------------------------------------------------
-- The report under each system
--
-- `unbox` asks that the image of what ran since boxing be `≾` the box's
-- grade. A run of 45 steps that read `High` data is the witness that
-- the systems differ.

module Checked (G : Grade) where

  open Grade G

  ≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
  ≾! _ _ {p} = toWitness p

  ⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! _ _ {p} = toWitnessFalse p

open _→ᵍ_ using (map)

tainted-run : Grade.Carrier left-sided-time×low-high
tainted-run = ([ 45 ,+∞⟩ , High)

-- embargo and taint check: the tainted run may not publish

module _ where
  open Grade left-sided-time×low-high
  open Checked left-sided-time×low-high

  withheld : ¬ (map (GradeSystem.∣ embargo-and-taint ∣ᵉ) tainted-run
                  ≾ ([ 30 ,+∞⟩ , Low))
  withheld = ⋠! tainted-run ([ 30 ,+∞⟩ , Low)

-- embargo only: the taint is forgotten, and the run may publish

module _ where
  open Grade left-sided-intervals
  open Checked left-sided-intervals

  forgets-taint : map (GradeSystem.∣ embargo ∣ᵉ) tainted-run ≡ [ 45 ,+∞⟩
  forgets-taint = refl

  published : map (GradeSystem.∣ embargo ∣ᵉ) tainted-run ≾ [ 30 ,+∞⟩
  published = ≾! [ 45 ,+∞⟩ [ 30 ,+∞⟩

-- taint check only: the run is refused whatever the time

module _ where
  open Grade two-point-levels
  open Checked two-point-levels

  refused : ¬ (map (GradeSystem.∣ taint ∣ᵉ) tainted-run ≾ Low)
  refused = ⋠! High Low
