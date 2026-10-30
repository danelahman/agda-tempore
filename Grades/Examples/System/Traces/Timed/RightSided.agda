------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.     --
--                                                                    --
-- The effect grades are the antichains of timed traces of            --
-- `Traces.Timed.RightSided`, read as upper bounds: every run of a    --
-- computation stays within one of the listed bounds. The resource    --
-- grades are the right-sided time intervals, "at most `n` time       --
-- steps".                                                            --
--                                                                    --
-- The projection measures a grade by its slowest bound:              --
--                                                                    --
--   ∣ P ∣ᵉ  =  [0, the greatest duration among the traces of P ]     --
--                                                                    --
-- The bound is sound, staying within a bound taking no longer than   --
-- the bound (`duration-≼ᵃ`), and optimal, each listed trace being a  --
-- run the grade permits. The resource grade forgets which runs there --
-- were and which operations they performed: `⌈ write ⌉` and `⟨ 3 ⟩`  --
-- have the same deadline, although only the first permits a store.   --
--                                                                    --
-- Monotonicity relates the two orders: weakening a grade replaces    --
-- each bound by one that permits at least as much, and a bound that  --
-- permits more takes at least as long.                               --
--                                                                    --
-- The two greatest grades correspond: `unbounded` permits any run    --
-- and `[0, ∞ ]` imposes no deadline. Both are absorbing, and the     --
-- projection preserves `_·_` at them.                                --
------------------------------------------------------------------------

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; ≤-antisym; ⊔-identityʳ)

open import Data.Unit using (tt)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Grades.Examples.Time.RightSided

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)

open import Data.Nat.Properties using (<⇒≢)

module Grades.Examples.System.Traces.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Data.List.Base using (List; _++_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Grades.Traces.Durations ℕᵀ Op
open import Grades.Traces.MaxDuration Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Grades.Traces.Allowance ℕᵀ Op costʰⁱ using (duration-≼ᵃ)

open import Grades.Examples.Traces.Timed.RightSided
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
  using (right-sided; right-sidedʰ; Bounds; within_; unbounded; _·ᵇ_; _⊔ᵇ_; _≾_; _≾₀_;
         Antichain; traces; nonempty; Trace; n; n-∈⁻; n-◃⁻; ◃-∈;
         _·ˢ_; _∙_; ⟨_⟩)

open MaxDurations costʰⁱ

------------------------------------------------------------------------
-- The reduction is invisible to the measure
--
-- It keeps a `≼`-maximal member above every member it drops, and a
-- more permissive bound takes no less, so the greatest duration is
-- attained on the reduced list just as it is on the original.

setDuration-n : (xs : List Trace) → setDuration (n xs) ≡ setDuration xs
setDuration-n xs = ≤-antisym below above
  where
    below : setDuration (n xs) ≤ setDuration xs
    below =
      bigMax-bound duration (n xs) (setDuration xs)
        (λ t t∈n → bigMax-mem duration t xs (n-∈⁻ t∈n))

    -- a member is met by a member of the reduction above it, which
    -- takes no less
    above : setDuration xs ≤ setDuration (n xs)
    above = bigMax-bound duration xs (setDuration (n xs)) step
      where
        step : (t : Trace) → t ∈ xs → duration t ≤ setDuration (n xs)
        step t t∈xs with find (n-◃⁻ xs (◃-∈ t∈xs))
        ... | t' , t'∈n , t≼t' =
              ≤-trans (duration-≼ᵃ t≼t')
                      (bigMax-mem duration t' (n xs) t'∈n)

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest bound, and the
-- unbounded grade by no deadline at all

mapₒ : Bounds → 𝕀ᵣ
mapₒ (within P) = [0, ↑ setDuration (traces P) ]
mapₒ unbounded  = [0, ∞ ]

-- monotonicity: each bound of `P` stays within one of `Q`, and so takes
-- no longer than it, hence no longer than `Q`'s slowest

mapₒ-monotone₀ : {P Q : Antichain} → P ≾₀ Q
               → setDuration (traces P) ≤ setDuration (traces Q)
mapₒ-monotone₀ {P} {Q} rel =
  bigMax-bound duration (traces P) (setDuration (traces Q)) step
  where
    step : (t : Trace) → t ∈ traces P → duration t ≤ setDuration (traces Q)
    step t t∈P
      with find (toWitness (rel t (fromWitness t∈P)))
    ... | t' , t'∈Q , t≼t' =
          ≤-trans (duration-≼ᵃ t≼t') (bigMax-mem duration t' (traces Q) t'∈Q)

mapₒ-monotone : {P Q : Bounds} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {within P}  {within Q}  rel = mapₒ-monotone₀ {P} {Q} rel
mapₒ-monotone {within _}  {unbounded} rel = tt
mapₒ-monotone {unbounded} {within _}  ()
mapₒ-monotone {unbounded} {unbounded} rel = tt

-- the monoid structure is preserved: sequencing two grades adds their
-- worst cases, the language product pairing each bound with each, and
-- both new points being absorbing

mapₒ-· : (P Q : Bounds) → mapₒ (P ·ᵇ Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· (within P) (within Q) =
  eq𝕀ᵣ (cong ↑_ (trans (setDuration-n (traces P ·ˢ traces Q))
                       (setDuration-·ˢ (traces P) (traces Q)
                                       (nonempty P) (nonempty Q))))
mapₒ-· (within _) unbounded  = refl
mapₒ-· unbounded  (within _) = refl
mapₒ-· unbounded  unbounded  = refl

-- joins are preserved: the slowest bound of a union is the slower of
-- the two slowest, and the unbounded grade absorbs

mapₒ-⊔ : (P Q : Bounds) → mapₒ (P ⊔ᵇ Q) ≡ mapₒ P ⊔ₒ mapₒ Q
mapₒ-⊔ (within P) (within Q) =
  eq𝕀ᵣ (cong ↑_ (trans (setDuration-n (traces P ++ traces Q))
                       (setDuration-++ (traces P) (traces Q))))
mapₒ-⊔ (within _) unbounded  = refl
mapₒ-⊔ unbounded  (within _) = refl
mapₒ-⊔ unbounded  unbounded  = refl

traces→right-sided-intervals : right-sided →ᵍ right-sided-intervals
traces→right-sided-intervals = strictᵍ record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-⊤        = refl
  ; map-⊔        = λ {P} {Q} → mapₒ-⊔ P Q
  ; map-of-dur   = λ {n} →
      eq𝕀ᵣ (cong ↑_ (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n)))
  }

tracesToRightSidedIntervalsGradeSystem : GradeSystem
tracesToRightSidedIntervalsGradeSystem = record
  { RGrade = right-sided-intervals
  ; EGrade = right-sided
  ; ∣_∣ᵉ   = traces→right-sided-intervals
  }

-- its hints

tracesToRightSidedIntervalsGradeSystemʰ : SystemHints tracesToRightSidedIntervalsGradeSystem
tracesToRightSidedIntervalsGradeSystemʰ = record
  { RHints      = right-sided-intervalsʰ
  ; EHints      = right-sidedʰ
  ; reflects-u? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
