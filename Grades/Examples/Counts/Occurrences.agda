------------------------------------------------------------------------
-- How often a timed trace draws on each counter.                     --
--                                                                    --
-- `index : Op → Fin n` assigns to each operation the counter it      --
-- draws on. At a bijection there is one counter per operation; a     --
-- coarser `index` pools operations into one quota. Delays draw on no --
-- counter.                                                           --
--                                                                    --
-- A count is additive for sequencing, so over a language product the --
-- greatest (and least) count is the sum of the greatest (and least)  --
-- counts of the factors: on each counter separately, the extreme is  --
-- attained by pairing an extreme member of each factor.              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Grades.Durations.Nat using (ℕᵀ)

module Grades.Examples.Counts.Occurrences
  (Op : Set) {n : ℕ} (index : Op → Fin n) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.Nat.Base using (zero; suc; _+_; _≤_)
open import Data.Nat.Properties
  using (+-assoc; +-identityʳ; ≤-antisym; ≤-trans; ≤-reflexive; +-mono-≤)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)

open import Grades.Traces.Base ℕᵀ Op
open import Grades.Examples.Counts.Extrema

open import Util.Equality

------------------------------------------------------------------------
-- Counting

-- one draw on counter `i`, or none

hit : Fin n → Op → ℕ
hit i o with index o ≟ i
... | yes _ = 1
... | no  _ = 0

-- an operation draws on its own counter

hit-index : (o : Op) → hit (index o) o ≡ 1
hit-index o with index o ≟ index o
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

mutual

  occ : Fin n → Trace → ℕ
  occ i ε               = 0
  occ i (operation o t) = hit i o + occ i t
  occ i (delay _ t)     = occ⁻ i t

  occ⁻ : Fin n → Trace⁻ → ℕ
  occ⁻ i ε⁻               = 0
  occ⁻ i (operation⁻ o t) = hit i o + occ i t

-- delays draw on nothing

occ-prepend : (i : Fin n) (d : D⁺) (t : Trace) → occ i (prepend d t) ≡ occ i t
occ-prepend i d ε               = refl
occ-prepend i d (operation o t) = refl
occ-prepend i d (delay e t)     = refl

occ-⟨⟩ : (i : Fin n) (k : ℕ) → occ i ⟨ k ⟩ ≡ 0
occ-⟨⟩ i zero    = refl
occ-⟨⟩ i (suc k) = refl

-- counts add up under sequencing

occ-∙ : (i : Fin n) (s t : Trace) → occ i (s ∙ t) ≡ occ i s + occ i t
occ-∙ i ε               t = refl
occ-∙ i (operation o s) t =
  trans (cong (hit i o +_) (occ-∙ i s t)) (sym (+-assoc (hit i o) (occ i s) (occ i t)))
occ-∙ i (delay d ε⁻)    t = occ-prepend i d t
occ-∙ i (delay d (operation⁻ o s)) t =
  trans (cong (hit i o +_) (occ-∙ i s t)) (sym (+-assoc (hit i o) (occ i s) (occ i t)))

------------------------------------------------------------------------
-- Extremes over a language product

private
  _·ˢ_ : List Trace → List Trace → List Trace
  xs ·ˢ ys = cartesianProductWith _∙_ xs ys

  -- a member of the product is a product of members, and back

  ·-mem : {x y : Trace} {xs ys : List Trace}
        → x ∈ xs → y ∈ ys → (x ∙ y) ∈ (xs ·ˢ ys)
  ·-mem = ∈-cartesianProductWith⁺ _∙_

maxOf-·ˢ : (i : Fin n) (xs ys : List Trace) → NonEmpty xs → NonEmpty ys
         → maxOf (occ i) (xs ·ˢ ys) ≡ maxOf (occ i) xs + maxOf (occ i) ys
maxOf-·ˢ i xs ys nx ny
  with maxOf-attained (occ i) xs nx | maxOf-attained (occ i) ys ny
... | x , x∈ , ex | y , y∈ , ey =
  ≤-antisym
    (maxOf-bound (occ i) (xs ·ˢ ys) bound)
    (≤-trans (≤-reflexive (trans (cong₂ _+_ ex ey) (sym (occ-∙ i x y))))
             (maxOf-mem (occ i) (·-mem x∈ y∈)))
  where
    bound : ∀ {w} → w ∈ (xs ·ˢ ys) → occ i w ≤ maxOf (occ i) xs + maxOf (occ i) ys
    bound m with ∈-cartesianProductWith⁻ _∙_ xs ys m
    ... | a , b , a∈ , b∈ , refl =
      ≤-trans (≤-reflexive (occ-∙ i a b))
              (+-mono-≤ (maxOf-mem (occ i) a∈) (maxOf-mem (occ i) b∈))

minOf-·ˢ : (i : Fin n) (xs ys : List Trace) → NonEmpty xs → NonEmpty ys
         → minOf (occ i) (xs ·ˢ ys) ≡ minOf (occ i) xs + minOf (occ i) ys
minOf-·ˢ i xs ys nx ny
  with minOf-attained (occ i) xs nx | minOf-attained (occ i) ys ny
... | x , x∈ , ex | y , y∈ , ey =
  ≤-antisym
    (≤-trans (minOf-mem (occ i) (·-mem x∈ y∈))
             (≤-reflexive (trans (occ-∙ i x y) (sym (cong₂ _+_ ex ey)))))
    (minOf-bound (occ i) (xs ·ˢ ys) (·ˢ-ne xs ys nx ny) bound)
  where
    ·ˢ-ne : (xs ys : List Trace) → NonEmpty xs → NonEmpty ys → NonEmpty (xs ·ˢ ys)
    ·ˢ-ne (x ∷ xs) (y ∷ ys) _ _ = _

    bound : ∀ {w} → w ∈ (xs ·ˢ ys) → minOf (occ i) xs + minOf (occ i) ys ≤ occ i w
    bound m with ∈-cartesianProductWith⁻ _∙_ xs ys m
    ... | a , b , a∈ , b∈ , refl =
      ≤-trans (+-mono-≤ (minOf-mem (occ i) a∈) (minOf-mem (occ i) b∈))
              (≤-reflexive (sym (occ-∙ i a b)))
