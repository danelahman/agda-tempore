--------------------------------------
-- Grades for effects and resources --
--------------------------------------

open import Util.Ordered.Bundles

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
