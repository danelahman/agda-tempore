------------------------------------------------------------------------
-- Hints for the solver.                                              --
--                                                                    --
-- What a grade or a grade system declares beyond its structure and   --
-- laws: properties it has, and candidate values for refuting. The    --
-- solver uses them to decide more; no declarative judgement depends  --
-- on them, entailment being semantic consequence in the grade        --
-- system. Each property is a proof under `Maybe`, `nothing` leaving  --
-- it undeclared.                                                     --
------------------------------------------------------------------------

module Grades.Hints where

open import Algebra.Definitions using (Commutative)
open import Data.List.Base using (List; [])
open import Data.Maybe.Base using (Maybe; nothing)
open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (Minimum)

open import Grades.Durations using (Duration)
open import Grades.Base

open import Util.Equality

-- Hints for a grade

record GradeHints {D : Duration} (G : Grade D) : Set where
  open Grade G
  field

    -- whether the unit is least
    𝟏-least? : Maybe (Minimum _≾_ 𝟏)

    -- commutativity of `_·_`; the trace grades leave it out, as there
    -- it depends on whether `Op` is empty
    ·-comm? : Maybe (Commutative _≃_ _·_)

    -- the closure of a grade
    plus? : (c : Carrier) → Maybe (Plus _·_ _≾_ c)

-- no hints

noGradeHints : {D : Duration} {G : Grade D} → GradeHints G
noGradeHints = record { 𝟏-least? = nothing ; ·-comm? = nothing ; plus? = λ _ → nothing }

-- commutativity on the nose

comm-≡ : {D : Duration} (G : Grade D)
       → Commutative _≡_ (Grade._·_ G) → Commutative (Grade._≃_ G) (Grade._·_ G)
comm-≡ G m c d = Grade.≃-reflexive G (m c d)

-- Hints for a grade system: those of its resource and effect grades,
-- and two of its own

record SystemHints (S : GradeSystem) : Set where
  open GradeSystem S
  open GradeSystemInterface S using (E; R; ∣_∣ᵉ; _≾ₑ_; _≾ᵣ_; 𝟏ₑ; 𝟏ᵣ)
  field

    RHints : GradeHints RGrade
    EHints : GradeHints EGrade

    -- whether `∣_∣ᵉ` reflects the order at the unit, `∣ e ∣ᵉ ≾ 𝟏` giving
    -- `e ≾ 𝟏`
    reflects-𝟏? : Maybe ((e : E) → ∣ e ∣ᵉ ≾ᵣ 𝟏ᵣ → e ≾ₑ 𝟏ₑ)

    -- candidate values of an effect rigid of a deferred condition, from
    -- the number of occurrences of the rigids on a side of an ordering
    -- (the degree) and the condition's resource and effect constants;
    -- any list is sound, the candidates serving only to refute
    witnesses : ℕ → List R → List E → List E

-- no hints

noSystemHints : {S : GradeSystem} → SystemHints S
noSystemHints = record
  { RHints = noGradeHints ; EHints = noGradeHints
  ; reflects-𝟏? = nothing ; witnesses = λ _ _ _ → [] }

-- The hints of a grade system, its grades' hints named as in
-- `GradeSystemInterface`

module SystemHintsInterface {S : GradeSystem} (H : SystemHints S) where

  open SystemHints H public

  open GradeHints RHints public renaming
    (𝟏-least? to 𝟏ᵣ-least?; ·-comm? to ·ᵣ-comm?; plus? to plusᵣ?)

  open GradeHints EHints public renaming
    (𝟏-least? to 𝟏ₑ-least?; ·-comm? to ·ₑ-comm?; plus? to plusₑ?)
