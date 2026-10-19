------------------------------------------------------------------------
-- Antichains of guarantees to at-least counts, at any trace order    --
-- that never covers a demand with fewer operations.                  --
--                                                                    --
--   ∣ P ∣ᵉ  =  on each counter, the least count among the            --
--              guarantees of P                                       --
--                                                                    --
-- The least count is taken because the set is read disjunctively:    --
-- one listed guarantee has been covered, and on each counter only    --
-- the smallest demand is certain. Each counter is minimised          --
-- separately.                                                        --
--                                                                    --
-- The one assumption is that `s ≼ t` (the run `t` covers `s`)        --
-- implies that `t` draws on every counter at least as often as `s`.  --
-- Under it the map is monotone, and the reduction to an antichain    --
-- preserves every least count, since a member it drops lies          --
-- `≼`-above one it keeps. Every field is preserved; the unit is the  --
-- greatest grade on both sides.                                      --
------------------------------------------------------------------------

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ; _≤_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order
import Syntax.Grades.Example.Counts.Occurrences as Occurrences

open import Syntax.Durations.Nat using (ℕᵀ)

module Syntax.Grades.Example.System.Counts.Lifted.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (O : Order.TraceOrder ℕᵀ Op)
  {n : ℕ} (index : Op → Fin n)
  (occ-mono : ∀ {s t} → Order.TraceOrder._≼_ O s t
            → (i : Fin n) → Occurrences.occ Op index i s ≤ Occurrences.occ Op index i t)
  where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec.Base using (Vec; tabulate)
open import Data.Vec.Properties using (tabulate-cong)

open import Syntax.Grades

open import Syntax.Grades.Example.Traces.Lifted.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans O
  using (left-sided; Antichain; traces; nonempty; _≾_; _·_; _⊔_; u; of-dur;
         Trace; ⟨_⟩; ε; ·ˢ-ne; ++-ne; n-ne; n-∈⁻; n-◃⁻; ◃-∈; ≾ˢ-◃)
  renaming (NonEmpty to NonEmptyˢ; _·ˢ_ to _⊙_; n to reduce)

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩; _⊔ₒ_)

open import Syntax.Grades.Example.Counts.AtLeast
open import Syntax.Grades.Example.Counts.Extrema
open Occurrences Op index

open Order.TraceOrder O using (_≼_)

------------------------------------------------------------------------
-- The projection

-- the count on counter `i` a list of guarantees makes certain

certain : List Trace → Fin n → 𝕀
certain xs i = atleast (minOf (occ i) xs)

mapₗ : Antichain → Vec 𝕀 n
mapₗ P = tabulate (certain (traces P))

-- the set-level non-emptiness is the list-level one

ne : (xs : List Trace) → NonEmptyˢ xs → NonEmpty xs
ne (_ ∷ _) _ = tt

------------------------------------------------------------------------
-- A trace with a member of `ys` below it draws on each counter at
-- least as often as the least of `ys`

below : (i : Fin n) {t : Trace} {ys : List Trace}
      → Any (_≼ t) ys → minOf (occ i) ys ≤ occ i t
below i p with find p
... | y , y∈ , y≼t = ≤-trans (minOf-mem (occ i) y∈) (occ-mono y≼t i)

-- so reducing a list to its antichain leaves every least count alone

certain-n : (xs : List Trace) → NonEmptyˢ xs → (i : Fin n)
          → certain (reduce xs) i ≡ certain xs i
certain-n xs nx i =
  cong atleast
    (minOf-cover (occ i) (reduce xs) xs (ne (reduce xs) (n-ne xs nx)) (ne xs nx)
      (λ {t} t∈ → minOf-mem (occ i) (n-∈⁻ {t} {xs} t∈))
      (λ t∈ → below i (n-◃⁻ xs (◃-∈ t∈))))

------------------------------------------------------------------------
-- Monotonicity: weakening lists easier guarantees, which demand no more

mapₗ-monotone : {P Q : Antichain} → P ≾ Q → mapₗ P ≾ᵛ mapₗ Q
mapₗ-monotone {P} {Q} rel =
  tabulate-≾ᵛ λ i →
    minOf-bound (occ i) (traces P) (ne (traces P) (nonempty P))
      (λ t∈ → below i (≾ˢ-◃ {traces P} {traces Q} rel t∈))

------------------------------------------------------------------------
-- The monoid structure: least counts add up along the product

mapₗ-· : (P Q : Antichain) → mapₗ (P · Q) ≡ mapₗ P ·ᵛ mapₗ Q
mapₗ-· P Q =
  trans (tabulate-cong λ i →
           trans (certain-n (traces P ⊙ traces Q) (·ˢ-ne (nonempty P) (nonempty Q)) i)
                 (cong atleast (minOf-·ˢ i (traces P) (traces Q)
                                         (ne (traces P) (nonempty P))
                                         (ne (traces Q) (nonempty Q)))))
        (tabulate-·ᵛ (certain (traces P)) (certain (traces Q)))

------------------------------------------------------------------------
-- Joins: the least count of a union is the lesser of the two

mapₗ-⊔ : (P Q : Antichain) → mapₗ (P ⊔ Q) ≡ mapₗ P ⊔ᵛ mapₗ Q
mapₗ-⊔ P Q =
  trans (tabulate-cong λ i →
           trans (certain-n (traces P ++ traces Q) (++-ne (nonempty P) (nonempty Q)) i)
                 (cong atleast (minOf-++ (occ i) (traces P) (traces Q)
                                         (ne (traces P) (nonempty P))
                                         (ne (traces Q) (nonempty Q)))))
        (tabulate-⊔ᵛ (certain (traces P)) (certain (traces Q)))

------------------------------------------------------------------------
-- Time draws on no counter

mapₗ-of-dur : (k : ℕ) → mapₗ (of-dur k) ≡ uᵛ
mapₗ-of-dur k = tabulate-uᵛ (certain (⟨ k ⟩ ∷ [])) (λ i → cong atleast (occ-⟨⟩ i k))

------------------------------------------------------------------------
-- The grade morphism and the grade system

left-sided→at-least-counts : left-sided →ᵍ at-least-counts n
left-sided→at-least-counts = record
  { map          = mapₗ
  ; map-monotone = λ {P} {Q} → mapₗ-monotone {P} {Q}
  ; map-u        = mapₗ-of-dur 0
  ; map-·        = λ {P} {Q} → mapₗ-· P Q
  ; map-⊤        = mapₗ-of-dur 0
  ; map-⊔        = λ {P} {Q} → mapₗ-⊔ P Q
  ; map-of-dur   = λ {k} → mapₗ-of-dur k
  }

leftSidedToAtLeastCountsGradeSystem : GradeSystem
leftSidedToAtLeastCountsGradeSystem = record
  { RGrade = at-least-counts n
  ; EGrade = left-sided
  ; ∣_∣ᵉ   = left-sided→at-least-counts
  ; reflects-u? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
