------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.     --
--                                                                    --
-- The effect grades are the antichains of timed traces of            --
-- `Traces.Timed.LeftSided`, read as guarantees: whatever a           --
-- computation did, it covered one of the listed traces. The resource --
-- grades are the left-sided time intervals, "at least `n` time       --
-- steps".                                                            --
--                                                                    --
-- The projection measures a grade by its fastest guarantee:          --
--                                                                    --
--   ∣ P ∣ᵉ  =  [ the least duration among the traces of P ,+∞⟩       --
--                                                                    --
-- The least duration is taken because the set is read disjunctively: --
-- of the listed traces, it is not known which was covered. The bound --
-- is sound, covering a trace taking at least as long as the trace    --
-- (`duration-≼ᶜ`), and optimal, each listed trace being a run the    --
-- grade admits.                                                      --
--                                                                    --
-- The resource grade forgets which operations were performed:        --
-- `⌈ write ⌉` and `⟨ 3 ⟩` become the same guarantee of elapsed time, --
-- although only the first guarantees a store.                        --
--                                                                    --
-- Monotonicity relates the two orders: weakening a grade replaces    --
-- each guarantee by a weaker one, which takes no longer, so the      --
-- least duration does not increase.                                  --
------------------------------------------------------------------------

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.LeftSided

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)

module Syntax.Grades.Example.System.Traces.Timed.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → ℕ) where

open import Data.List.Base using (List; _++_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades.Traces.Durations ℕᵀ Op
open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Syntax.Grades.Traces.Coverage ℕᵀ Op costˡᵒ using (duration-≼ᶜ)

open import Syntax.Grades.Example.Traces.Timed.LeftSided
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (left-sided; _≾_; Antichain; traces; nonempty; _·_; _⊔_;
         Trace; NonEmpty; n; n-ne; n-∈⁻; n-◃⁻; ◃-∈; _·ˢ_; ·ˢ-ne; ++-ne)

open MinDurations costˡᵒ

------------------------------------------------------------------------
-- The reduction is invisible to the measure
--
-- It keeps a `≼`-minimal member of every member it drops, and an
-- easier guarantee takes no longer, so the least duration is attained
-- on the reduced list just as it is on the original.

minSetDuration-n : (xs : List Trace) → NonEmpty xs
                 → minSetDuration (n xs) ≡ minSetDuration xs
minSetDuration-n xs ne = ≤-antisym below above
  where
    -- a member is met by a member of the reduction below it, which
    -- takes no longer
    below : minSetDuration (n xs) ≤ minSetDuration xs
    below = bigMin-bound duration xs (minSetDuration (n xs)) ne step
      where
        step : (t : Trace) → t ∈ xs → minSetDuration (n xs) ≤ duration t
        step t t∈xs with find (n-◃⁻ xs (◃-∈ t∈xs))
        ... | t' , t'∈n , t'≼t =
              ≤-trans (bigMin-mem duration t' (n xs) t'∈n) (duration-≼ᶜ t'≼t)

    above : minSetDuration xs ≤ minSetDuration (n xs)
    above =
      bigMin-bound duration (n xs) (minSetDuration xs) (n-ne xs ne)
        (λ t t∈n → bigMin-mem duration t xs (n-∈⁻ t∈n))

------------------------------------------------------------------------
-- The projection: a grade is measured by its fastest guarantee

mapₒ : Antichain → 𝕀
mapₒ P = [ minSetDuration (traces P) ,+∞⟩

-- monotonicity: each guarantee of `P` is weakened by one of `Q`, which
-- therefore takes no longer, hence at least `Q`'s fastest

mapₒ-monotone : {P Q : Antichain} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {P} {Q} rel =
  bigMin-bound duration (traces P) (minSetDuration (traces Q)) (nonempty P) step
  where
    step : (t : Trace) → t ∈ traces P → minSetDuration (traces Q) ≤ duration t
    step t t∈P
      with find (toWitness (rel t (fromWitness t∈P)))
    ... | t' , t'∈Q , t'≼t =
          ≤-trans (bigMin-mem duration t' (traces Q) t'∈Q) (duration-≼ᶜ t'≼t)

-- the monoid structure is preserved: sequencing two grades adds their
-- best cases, the language product pairing each guarantee with each

mapₒ-· : (P Q : Antichain) → mapₒ (P · Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· P Q =
  eq𝕀 (trans (minSetDuration-n (traces P ·ˢ traces Q)
                (·ˢ-ne (nonempty P) (nonempty Q)))
             (minSetDuration-·ˢ (traces P) (traces Q)
                (nonempty P) (nonempty Q)))

-- joins are preserved: the fastest guarantee of a union is the faster
-- of the two fastest

mapₒ-⊔ : (P Q : Antichain) → mapₒ (P ⊔ Q) ≡ mapₒ P ⊔ₒ mapₒ Q
mapₒ-⊔ P Q =
  eq𝕀 (trans (minSetDuration-n (traces P ++ traces Q)
                (++-ne (nonempty P) (nonempty Q)))
             (minSetDuration-++ (traces P) (traces Q)
                (nonempty P) (nonempty Q)))

traces→left-sided-intervals : left-sided →ᵍ left-sided-intervals
traces→left-sided-intervals = strictᵍ record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-⊤        = refl
  ; map-⊔        = λ {P} {Q} → mapₒ-⊔ P Q
  ; map-of-dur   = λ {n} → eq𝕀 (duration-⟨⟩ n)
  }

tracesToLeftSidedIntervalsGradeSystem : GradeSystem
tracesToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals
  ; EGrade = left-sided
  ; ∣_∣ᵉ   = traces→left-sided-intervals
  ; reflects-u? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
