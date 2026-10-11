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

open import Data.Maybe.Base using (just)

open import Syntax.Durations using (Duration)
open import Syntax.Grades

open import Util.Equality

-- the identity grade morphism

idᵍ : {D : Duration} (G : Grade D) → G →ᵍ G
idᵍ G = record
  { map          = λ c → c
  ; map-monotone = λ rel → rel
  ; map-u        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-of-dur   = refl
  }

-- a grade, read as both the effect grades and the resource grades; the
-- identity reflects the order at the unit

identityGradeSystem : {D : Duration} → Grade D → GradeSystem
identityGradeSystem {D} G = record
  { Dur    = D
  ; RGrade = G
  ; EGrade = G
  ; ∣_∣ᵉ   = idᵍ G
  ; reflects-u? = just (λ e p → p)
  }
