------------------------------------------------------------------------
-- The grade system in which effects and resources are graded alike.  --
--                                                                    --
-- Both components are the same ordered monoid and the projection is  --
-- the identity, so `mapᵉ` disappears from the typing rules: the lock --
-- a computation places on the context is its effect grade, and the   --
-- premise of `unbox` compares what a computation did directly with   --
-- the grade of the box.                                              --
------------------------------------------------------------------------

module Grades.Examples.System.Identity where

open import Data.List.Base using (List; []; _++_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ)

open import Grades.Durations using (Duration)
open import Grades.Base
open import Grades.Hints using (GradeHints; SystemHints)

open import Util.Equality

-- the identity grade morphism

idᵍ : {D : Duration} (G : Grade D) → G →ᵍ G
idᵍ G = strictᵍ record
  { map          = λ c → c
  ; map-monotone = λ rel → rel
  ; map-u        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-of-dur   = refl
  }

-- a grade, read as both the effect grades and the resource grades

identityGradeSystem : {D : Duration} → Grade D → GradeSystem
identityGradeSystem {D} G = record
  { Dur    = D
  ; RGrade = G
  ; EGrade = G
  ; ∣_∣ᵉ   = idᵍ G
  }

-- its hints: the grade's for both sorts, and the identity reflects the
-- order at the unit. The candidates for a rigid are the grade's own
-- (`wit`), for the constants of both sorts.

identityʰ : {D : Duration} {G : Grade D} → GradeHints G
          → (ℕ → List (Grade.Carrier G) → List (Grade.Carrier G))
          → SystemHints (identityGradeSystem G)
identityʰ H wit = record
  { RHints      = H
  ; EHints      = H
  ; reflects-u? = just (λ e p → p)
  ; witnesses   = λ d rcs ecs → wit d (rcs ++ ecs)
  }

-- no candidates of a grade's own

noWitnesses : {A : Set} → ℕ → List A → List A
noWitnesses _ _ = []
