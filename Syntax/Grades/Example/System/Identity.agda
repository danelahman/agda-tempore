------------------------------------------------------------------------
-- The grade system in which effects and resources are graded alike.  --
--                                                                    --
-- Both components are the same ordered monoid and the projection is  --
-- the identity, so `mapᵉ` disappears from the typing rules: the lock --
-- a computation places on the context is its effect grade, and the   --
-- premise of `unbox` compares what a computation did directly with   --
-- the grade of the box.                                              --
------------------------------------------------------------------------

module Syntax.Grades.Example.System.Identity where

open import Syntax.Grades

open import Util.Equality

-- the identity grade morphism

idᵍ : (G : Grade) → G →ᵍ G
idᵍ G = record
  { map          = λ c → c
  ; map-monotone = λ rel → rel
  ; map-u        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-of-nat   = refl
  }

-- a grade, read as both the effect grades and the resource grades

identityGradeSystem : Grade → GradeSystem
identityGradeSystem G = record
  { RGrade = G
  ; EGrade = G
  ; ∣_∣ᵉ   = idᵍ G
  }
