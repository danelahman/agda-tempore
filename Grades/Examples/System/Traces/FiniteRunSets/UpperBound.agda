------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.     --
--                                                                    --
-- The effect grades are the finite run set grade of upper bounds:    --
-- every run of a computation is one of the listed traces. The        --
-- resource grades are the upper bounds on time, "at most `n`         --
-- time steps".                                                       --
--                                                                    --
--   ∣ Q ∣ᵉ  =  [0, the greatest duration among the traces of Q ]     --
--                                                                    --
-- The greatest duration is taken because the set is read             --
-- disjunctively: the deadline covers the slowest run. The resource   --
-- grade forgets which runs there were, so `⌈ write ⌉` and `⟨ 3 ⟩`,   --
-- distinct and incomparable as effect grades (the comparison of      --
-- traces being equality), have the same deadline.                    --
--                                                                    --
-- Monotonicity holds because weakening adds runs to the list, and a  --
-- longer list has a greater maximum.                                 --
--                                                                    --
-- The two greatest grades correspond: `any-run` permits any run and  --
-- `[0, ∞ ]` imposes no deadline, and both are absorbing.             --
------------------------------------------------------------------------

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (⊔-identityʳ)

open import Data.Unit using (tt)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Grades.Base
open import Grades.Hints using (SystemHints; noGradeHints)
open import Grades.Examples.Time.UpperBound
  renaming (upper-bound to time-upper-bound; upper-boundʰ to time-upper-boundʰ)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)

module Grades.Examples.System.Traces.FiniteRunSets.UpperBound
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → ℕ) where

open import Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Grades.Traces.Durations ℕᵀ Op
open import Grades.Traces.MaxDuration Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans

open import Grades.Examples.Traces.FiniteRunSets.UpperBound
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (upper-bound; Permits; permitting_; any-run; _·ᵖ_; _⊔ᵖ_; _≾_; _≾₀_)

open MaxDurations costʰⁱ

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest listed run, and
-- the unrestricted grade by no deadline at all

mapₒ : Permits → 𝕀ᵣ
mapₒ (permitting Q) = [0, ↑ setDuration (traces Q) ]
mapₒ any-run        = [0, ∞ ]

mapₒ-monotone₀ : {P Q : NeTraces} → P ≾₀ Q
               → setDuration (traces P) ≤ setDuration (traces Q)
mapₒ-monotone₀ {P} {Q} rel = setDuration-⊑ (traces P) (traces Q) rel

mapₒ-monotone : {P Q : Permits} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {permitting P} {permitting Q} rel = mapₒ-monotone₀ {P} {Q} rel
mapₒ-monotone {permitting _} {any-run}      rel = tt
mapₒ-monotone {any-run}      {permitting _} ()
mapₒ-monotone {any-run}      {any-run}      rel = tt

-- the monoid structure is preserved: sequencing two grades adds their
-- worst cases, the language product pairing each run with each, and
-- both new points being absorbing

mapₒ-· : (P Q : Permits) → mapₒ (P ·ᵖ Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· (permitting P) (permitting Q) =
  eq𝕀ᵣ (cong ↑_ (setDuration-nf-·ˢ (traces P) (traces Q)
                                   (nonempty P) (nonempty Q)))
mapₒ-· (permitting _) any-run        = refl
mapₒ-· any-run        (permitting _) = refl
mapₒ-· any-run        any-run        = refl

-- joins are preserved: the slowest run of a union is the slower of the
-- two slowest, and the unrestricted grade absorbs

mapₒ-⊔ : (P Q : Permits) → mapₒ (P ⊔ᵖ Q) ≡ mapₒ P ⊔ₒ mapₒ Q
mapₒ-⊔ (permitting P) (permitting Q) =
  eq𝕀ᵣ (cong ↑_ (setDuration-∪ˢ (traces P) (traces Q)))
mapₒ-⊔ (permitting _) any-run        = refl
mapₒ-⊔ any-run        (permitting _) = refl
mapₒ-⊔ any-run        any-run        = refl

finite-run-sets→upper-bounds : upper-bound →ᵍ time-upper-bound
finite-run-sets→upper-bounds = strictᵍ record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-𝟏        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-⊤        = refl
  ; map-⊔        = λ {P} {Q} → mapₒ-⊔ P Q
  ; map-ι        = λ {n} →
      eq𝕀ᵣ (cong ↑_ (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n)))
  }

finite-run-sets→upper-bounds-grade-system : GradeSystem
finite-run-sets→upper-bounds-grade-system = record
  { RGrade = time-upper-bound
  ; EGrade = upper-bound
  ; ∣-∣ᵉ   = finite-run-sets→upper-bounds
  }

-- its hints

finite-run-sets→upper-bounds-grade-systemʰ : SystemHints finite-run-sets→upper-bounds-grade-system
finite-run-sets→upper-bounds-grade-systemʰ = record
  { RHints      = time-upper-boundʰ
  ; EHints      = noGradeHints
  ; reflects-𝟏? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
