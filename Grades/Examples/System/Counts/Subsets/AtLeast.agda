------------------------------------------------------------------------
-- The subset cap, read as certain counts.                            --
--                                                                    --
-- Every run of a computation is listed, so on each counter the least --
-- count among the listed runs is certain:                            --
--                                                                    --
--   ∣ Q ∣ᵉ  =  on each counter, the least count among the traces     --
--              of Q                                                  --
--                                                                    --
-- The greatest grade `any-run` of the cap is absorbing, and a        --
-- morphism sends it to the greatest grade. In the at-least counts    --
-- that is the unit, and an absorbing element sent to the unit makes  --
-- every morphism into them constant (`collapses`). The target is     --
-- therefore the counts with a formal greatest grade on each counter: --
-- `any-run` is sent to `no-claim` on every counter, which is         --
-- absorbing, and every field is preserved.                           --
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

module Grades.Examples.System.Counts.Subsets.AtLeast
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  {n : ℕ} (index : Op → Fin n) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Unit using (tt)
open import Data.Vec.Base using (Vec; tabulate)
open import Data.Vec.Properties using (tabulate-cong)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Grades.Durations using (Duration)
open import Grades.Base

open import Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (Trace; traces; nonempty; nf; nf-ne; nf-∈⁺; nf-∈⁻; ⟨_⟩; ·ˢ-ne; ++-ne)
  renaming (NonEmpty to NonEmptyˢ; _·ˢ_ to _⊙_)

open import Grades.Examples.Traces.Subsets.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (right-sided; Permits; permitting_; any-run; _·ᵖ_; _⊔ᵖ_; _≾_)

open import Grades.Examples.Time.LeftSided using (𝕀⊤; timed_; untimed; _·ᵗ_; ≾ᵗ-antisym)

open import Grades.Examples.Counts.AtLeast
  using (at-least-counts; at-least-counts-with-⊤; certainly; module WithTop)
open WithTop
open import Grades.Examples.Counts.Extrema
open import Grades.Examples.Counts.Occurrences Op index

------------------------------------------------------------------------
-- An absorbing greatest grade sent to the unit collapses a morphism

collapses : {D : Duration} (G H : Grade D)
          → (∀ c → Grade._·_ G (Grade.⊤ G) c ≡ Grade.⊤ G)
          → Grade.⊤ H ≡ Grade.u H
          → (F : G →ᵍ H) (c : Grade.Carrier G) → Grade._≃_ H (_→ᵍ_.map F c) (Grade.u H)
collapses G H absorb top-unit F c =
  ≃-trans (≃-sym (·-identityˡ (map c)))
  (≃-trans (·-cong (≃-sym top≃u) ≃-refl)
  (≃-trans (≃-sym map-·)
  (≃-trans (≃-reflexive (cong map (absorb c)))
           top≃u)))
  where
    open _→ᵍ_ F
    open Grade H using (≃-trans; ≃-sym; ≃-refl; ≃-reflexive; ·-cong; ·-identityˡ)
    top≃u : Grade._≃_ H (map (Grade.⊤ G)) (Grade.u H)
    top≃u = ≃-trans map-⊤ (≃-reflexive top-unit)

-- so every morphism from the cap into the at-least counts is constant

constant : (F : right-sided →ᵍ at-least-counts n) (P : Permits)
         → Grade._≃_ (at-least-counts n) (_→ᵍ_.map F P) (Grade.u (at-least-counts n))
constant = collapses right-sided (at-least-counts n) (λ _ → refl) refl

------------------------------------------------------------------------
-- The projection, into the counts with a formal greatest grade

certain : List Trace → Fin n → 𝕀⊤
certain xs i = certainly (minOf (occ i) xs)

mapₗ : Permits → Vec 𝕀⊤ n
mapₗ (permitting Q) = tabulate (certain (traces Q))
mapₗ any-run        = ⊤ᵛ

ne : (xs : List Trace) → NonEmptyˢ xs → NonEmpty xs
ne (_ ∷ _) _ = tt

certain-nf : (xs : List Trace) → NonEmptyˢ xs → (i : Fin n)
           → certain (nf xs) i ≡ certain xs i
certain-nf xs nx i =
  cong certainly
    (minOf-same (occ i) (nf xs) xs (ne (nf xs) (nf-ne xs nx)) (ne xs nx)
                (λ {t} → nf-∈⁻ {t} {xs}) (λ {t} → nf-∈⁺ {t} {xs}))

-- monotonicity: adding runs can only lower the least count

mapₗ-monotone : {P Q : Permits} → P ≾ Q → mapₗ P ≾ᵛ mapₗ Q
mapₗ-monotone {permitting P} {permitting Q} rel =
  tabulate-≾ᵛ λ i →
    minOf-bound (occ i) (traces P) (ne (traces P) (nonempty P))
      (λ t∈ → minOf-mem (occ i) (toWitness (rel _ (fromWitness t∈))))
mapₗ-monotone {permitting _} {any-run}      _  = ≾ᵛ-⊤ _
mapₗ-monotone {any-run}      {permitting _} ()
mapₗ-monotone {any-run}      {any-run}      _  = ≾ᵛ-refl

-- the monoid structure, `no-claim` absorbing

absorbʳ : (a : 𝕀⊤) → a ·ᵗ untimed ≡ untimed
absorbʳ (timed _) = refl
absorbʳ untimed   = refl

mapₗ-· : (P Q : Permits) → mapₗ (P ·ᵖ Q) ≡ mapₗ P ·ᵛ mapₗ Q
mapₗ-· (permitting P) (permitting Q) =
  trans (tabulate-cong λ i →
           trans (certain-nf (traces P ⊙ traces Q) (·ˢ-ne (nonempty P) (nonempty Q)) i)
                 (cong certainly (minOf-·ˢ i (traces P) (traces Q)
                                           (ne (traces P) (nonempty P))
                                           (ne (traces Q) (nonempty Q)))))
        (tabulate-·ᵛ (certain (traces P)) (certain (traces Q)))
mapₗ-· (permitting P) any-run = sym (·ᵛ-⊤ᵛ absorbʳ (mapₗ (permitting P)))
mapₗ-· any-run        Q       = sym (⊤ᵛ-·ᵛ (λ _ → refl) (mapₗ Q))

-- joins: the least count of a union is the lesser of the two

mapₗ-⊔ : (P Q : Permits) → mapₗ (P ⊔ᵖ Q) ≡ mapₗ P ⊔ᵛ mapₗ Q
mapₗ-⊔ (permitting P) (permitting Q) =
  trans (tabulate-cong λ i →
           trans (certain-nf (traces P ++ traces Q) (++-ne (nonempty P) (nonempty Q)) i)
                 (cong certainly (minOf-++ (occ i) (traces P) (traces Q)
                                           (ne (traces P) (nonempty P))
                                           (ne (traces Q) (nonempty Q)))))
        (tabulate-⊔ᵛ (certain (traces P)) (certain (traces Q)))
mapₗ-⊔ (permitting P) any-run = sym (⊔ᵛ-⊤ᵛ (⊔-⊤-≡ ≾ᵗ-antisym) (mapₗ (permitting P)))
mapₗ-⊔ any-run        Q       = sym (⊤ᵛ-⊔ᵛ (⊤-⊔-≡ ≾ᵗ-antisym) (mapₗ Q))

-- time draws on no counter

mapₗ-of-dur : (k : ℕ) → mapₗ (Grade.of-dur right-sided k) ≡ uᵛ
mapₗ-of-dur k =
  tabulate-uᵛ (certain (⟨ k ⟩ ∷ [])) (λ i → cong certainly (occ-⟨⟩ i k))

------------------------------------------------------------------------
-- The grade morphism and the grade system

subsets→at-least-counts-with-⊤ : right-sided →ᵍ at-least-counts-with-⊤ n
subsets→at-least-counts-with-⊤ = strictᵍ record
  { map          = mapₗ
  ; map-monotone = λ {P} {Q} → mapₗ-monotone {P} {Q}
  ; map-u        = mapₗ-of-dur 0
  ; map-·        = λ {P} {Q} → mapₗ-· P Q
  ; map-⊤        = refl
  ; map-⊔        = λ {P} {Q} → mapₗ-⊔ P Q
  ; map-of-dur   = λ {k} → mapₗ-of-dur k
  }

subsetsToAtLeastCountsGradeSystem : GradeSystem
subsetsToAtLeastCountsGradeSystem = record
  { RGrade = at-least-counts-with-⊤ n
  ; EGrade = right-sided
  ; ∣_∣ᵉ   = subsets→at-least-counts-with-⊤
  ; reflects-u? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
