--------------------------------------
-- Grades for effects and resources --
--------------------------------------

open import Util.Ordered.Bundles

open import Level

module Syntax.Grades where

--Grade : Set₁
--Grade = CommutativePomonoid zero zero zero 

record Grade : Set₁ where

  field

    Carrier : Set₀

    -- monoid ops

    -- order

    -- monoid is ordered

    -- ...

    -- inclusion of ℕ (d : ℕ → Carrier s.t. ... ? ...)

    -- ...


open Grade

record _→ᵍ_ (G G' : Grade) : Set₁ where

  field

    map : Carrier G → Carrier G'

    -- laws
    

record GradeSystem : Set₂ where

  field

    RGrade : Grade
    EGrade : Grade
    ∣_∣ : EGrade →ᵍ RGrade
  

{-
module Syntax.Grades
  {cₑ ℓ₁ ℓ₂} {E : Set cₑ} -- The underlying set (effects)
  {cᵣ ℓ₃ ℓ₄} {R : Set cᵣ} -- The underlying set (resources)
  {cpomₑ : CommutativePomonoid cₑ ℓ₁ ℓ₂}
  {cpomᵣ : CommutativePomonoid cᵣ ℓ₃ ℓ₄}
  where

open import Relation.Binary
open import Util.Ordered.Structures
open import Agda.Primitive
open import Algebra.Core

-- Grades for effects
Timeₑ : Set cₑ
Timeₑ = Carrierₑ
  where open CommutativePomonoid cpomₑ renaming (Carrier to Carrierₑ)
  
-- Grades for resources
Timeᵣ : Set cᵣ
Timeᵣ = Carrierᵣ
  where open CommutativePomonoid cpomᵣ renaming (Carrier to Carrierᵣ)

-- Old version:
-- Timeᵣ : Set (lsuc (cᵣ ⊔ ℓ₃ ⊔ ℓ₄))
-- Timeᵣ = CommutativePomonoid cᵣ ℓ₃ ℓ₄
-}
