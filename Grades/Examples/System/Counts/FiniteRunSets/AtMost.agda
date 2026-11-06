------------------------------------------------------------------------
-- A grade system in which the resource grades are quotas.            --
--                                                                    --
-- The effect grades are the finite run set grade of upper bounds:    --
-- every run of a computation is one of the listed traces. The        --
-- resource grades are at-most counts, one quota per counter.         --
--                                                                    --
--   ∣ Q ∣ᵉ  =  on each counter, the greatest count among the traces  --
--              of Q                                                  --
--                                                                    --
-- The greatest count is taken because the set is read disjunctively: --
-- each quota covers the run that draws on it most. Each counter is   --
-- maximised separately, so `⌈ read ⌉` and `⌈ send ⌉` together        --
-- project to one of each, more than either run performs. The         --
-- resource grade forgets which runs there were and where their       --
-- operations and delays occur.                                       --
--                                                                    --
-- Every field is preserved. The two greatest grades correspond:      --
-- `any-run` permits any run and `unlimited` on every counter imposes --
-- no quota, and both are absorbing. Time draws on no counter, so the --
-- pure delays project to the unit.                                   --
------------------------------------------------------------------------

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)

module Grades.Examples.System.Counts.FiniteRunSets.AtMost
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  {n : ℕ} (index : Op → Fin n) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Properties using (⊔-identityʳ)
open import Data.Unit using (tt)
open import Data.Vec.Base using (Vec; tabulate)
open import Data.Vec.Properties using (tabulate-cong)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Grades.Base
open import Grades.Hints using (SystemHints; noGradeHints)

open import Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (Trace; traces; nonempty; nf; nf-∈⁺; nf-∈⁻; ⟨_⟩)
  renaming (NonEmpty to NonEmptyˢ; _·ˢ_ to _⊙_)

open import Grades.Examples.Traces.FiniteRunSets.UpperBound
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (upper-bound; Permits; permitting_; any-run; _·ᵖ_; _⊔ᵖ_; _≾_)

open import Grades.Examples.Time.UpperBound
  using (𝕀ᵣ; [0,_]; ↑_; ∞; _·ₒ_; ≾ₒ-antisym)

open import Grades.Examples.Counts.AtMost
open import Grades.Examples.Counts.Extrema
open import Grades.Examples.Counts.Occurrences Op index

------------------------------------------------------------------------
-- The projection

-- the quota on counter `i` a list of runs needs

need : List Trace → Fin n → 𝕀ᵣ
need xs i = upto (maxOf (occ i) xs)

mapₒ : Permits → Vec 𝕀ᵣ n
mapₒ (permitting Q) = tabulate (need (traces Q))
mapₒ any-run        = ⊤ᵛ

-- the set-level non-emptiness is the list-level one

ne : (xs : List Trace) → NonEmptyˢ xs → NonEmpty xs
ne (_ ∷ _) _ = tt

------------------------------------------------------------------------
-- Monotonicity: weakening adds runs, and a longer list has a greater
-- maximum on every counter

mapₒ-monotone : {P Q : Permits} → P ≾ Q → mapₒ P ≾ᵛ mapₒ Q
mapₒ-monotone {permitting P} {permitting Q} rel =
  tabulate-≾ᵛ λ i →
    maxOf-bound (occ i) (traces P)
      (λ t∈ → maxOf-mem (occ i) (toWitness (rel _ (fromWitness t∈))))
mapₒ-monotone {permitting _} {any-run}      _  = ≾ᵛ-⊤ _
mapₒ-monotone {any-run}      {permitting _} ()
mapₒ-monotone {any-run}      {any-run}      _  = ≾ᵛ-refl

------------------------------------------------------------------------
-- The monoid structure: counts add up along the language product, and
-- both new points are absorbing

⊤-absorbˡ : (a : 𝕀ᵣ) → [0, ∞ ] ·ₒ a ≡ [0, ∞ ]
⊤-absorbˡ [0, _ ] = refl

⊤-absorbʳ : (a : 𝕀ᵣ) → a ·ₒ [0, ∞ ] ≡ [0, ∞ ]
⊤-absorbʳ [0, ↑ _ ] = refl
⊤-absorbʳ [0, ∞ ]   = refl

need-nf : (xs : List Trace) (i : Fin n) → need (nf xs) i ≡ need xs i
need-nf xs i =
  cong upto (maxOf-same (occ i) (nf xs) xs (λ {t} → nf-∈⁻ {t} {xs}) (λ {t} → nf-∈⁺ {t} {xs}))

mapₒ-· : (P Q : Permits) → mapₒ (P ·ᵖ Q) ≡ mapₒ P ·ᵛ mapₒ Q
mapₒ-· (permitting P) (permitting Q) =
  trans (tabulate-cong λ i →
           trans (need-nf (traces P ⊙ traces Q) i)
                 (cong upto (maxOf-·ˢ i (traces P) (traces Q)
                                      (ne (traces P) (nonempty P))
                                      (ne (traces Q) (nonempty Q)))))
        (tabulate-·ᵛ (need (traces P)) (need (traces Q)))
mapₒ-· (permitting P) any-run        = sym (·ᵛ-⊤ᵛ ⊤-absorbʳ (mapₒ (permitting P)))
mapₒ-· any-run        Q              = sym (⊤ᵛ-·ᵛ ⊤-absorbˡ (mapₒ Q))

------------------------------------------------------------------------
-- Joins: the greatest count in a union is the greater of the two, and
-- `any-run` absorbs

mapₒ-⊔ : (P Q : Permits) → mapₒ (P ⊔ᵖ Q) ≡ mapₒ P ⊔ᵛ mapₒ Q
mapₒ-⊔ (permitting P) (permitting Q) =
  trans (tabulate-cong λ i →
           trans (need-nf (traces P ++ traces Q) i)
                 (cong upto (maxOf-++ (occ i) (traces P) (traces Q))))
        (tabulate-⊔ᵛ (need (traces P)) (need (traces Q)))
mapₒ-⊔ (permitting P) any-run        = sym (⊔ᵛ-⊤ᵛ (⊔-⊤-≡ ≾ₒ-antisym) (mapₒ (permitting P)))
mapₒ-⊔ any-run        Q              = sym (⊤ᵛ-⊔ᵛ (⊤-⊔-≡ ≾ₒ-antisym) (mapₒ Q))

------------------------------------------------------------------------
-- Time draws on no counter

mapₒ-ι : (k : ℕ) → mapₒ (Grade.ι upper-bound k) ≡ 𝟏ᵛ
mapₒ-ι k =
  tabulate-𝟏ᵛ (need (⟨ k ⟩ ∷ []))
    (λ i → cong upto (trans (⊔-identityʳ (occ i ⟨ k ⟩)) (occ-⟨⟩ i k)))

------------------------------------------------------------------------
-- The grade morphism and the grade system

finite-run-sets→at-most-counts : upper-bound →ᵍ at-most-counts n
finite-run-sets→at-most-counts = strictᵍ record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-𝟏        = mapₒ-ι 0
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-⊤        = refl
  ; map-⊔        = λ {P} {Q} → mapₒ-⊔ P Q
  ; map-ι        = λ {k} → mapₒ-ι k
  }

finite-run-sets→at-most-counts-grade-system : GradeSystem
finite-run-sets→at-most-counts-grade-system = record
  { RGrade = at-most-counts n
  ; EGrade = upper-bound
  ; ∣-∣ᵉ   = finite-run-sets→at-most-counts
  }

-- its hints

finite-run-sets→at-most-counts-grade-systemʰ : SystemHints finite-run-sets→at-most-counts-grade-system
finite-run-sets→at-most-counts-grade-systemʰ = record
  { RHints      = (at-most-countsʰ n)
  ; EHints      = noGradeHints
  ; reflects-𝟏? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
