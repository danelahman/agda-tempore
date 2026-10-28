------------------------------------------------------------------------
-- The operations of the worked finite-expression grades, with        --
-- running times in dense time, ends open or closed:                  --
--                                                                    --
--   heat   [2, 4]                                                    --
--   cool   ]1, 2[    more than one unit, less than two               --
--   log    ]1/4, 1/2]                                                --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.Rigid.Finite.Operations where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product using (_,_)
open import Relation.Nullary.Decidable using (toWitness)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ)
open import Grades.Examples.Time.Dense.TwoSided
  using (Interval; [_,_]; ]_,_]; ]_,_[; ↑_; _/_; #_; _⊑?_; 0⁺; lo)
open import Grades.Traces.RunningTimes ℚ≥0ᵀ using (RunningTimes) renaming (fin to bounded)
open import Grades.Durations.Intervals.Dense ℚ≥0ᵀ using (_∈ⁱ?_)

data Op : Set where
  heat cool log : Op

code : Op → Fin 3
code heat = zero
code cool = suc zero
code log  = suc (suc zero)

name : Fin 3 → Op
name zero             = heat
name (suc zero)       = cool
name (suc (suc zero)) = log

name-code : ∀ o → name (code o) ≡ o
name-code heat = refl
name-code cool = refl
name-code log  = refl

code-name : ∀ c → code (name c) ≡ c
code-name zero             = refl
code-name (suc zero)       = refl
code-name (suc (suc zero)) = refl

rt : Op → Interval
rt heat = [ # 2 , ↑ # 4 ]
rt cool = ] # 1 , ↑ # 2 [
rt log  = ] 1 / 4 , ↑ 1 / 2 ]

running : RunningTimes Op
running = record
  { rt          = rt
  ; rt-bounded  = λ { heat → bounded _ ; cool → bounded _ ; log → bounded _ }
  ; rt-positive = λ { heat → toWitness {a? = 0⁺ ⊑? lo (rt heat)} _
                    ; cool → toWitness {a? = 0⁺ ⊑? lo (rt cool)} _
                    ; log  → toWitness {a? = 0⁺ ⊑? lo (rt log)} _ }
  ; rt-inhabited = λ { heat → # 2 , toWitness {a? = # 2 ∈ⁱ? rt heat} _
                     ; cool → 3 / 2 , toWitness {a? = 3 / 2 ∈ⁱ? rt cool} _
                     ; log  → 1 / 2 , toWitness {a? = 1 / 2 ∈ⁱ? rt log} _ }
  }
