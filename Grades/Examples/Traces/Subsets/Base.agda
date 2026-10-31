------------------------------------------------------------------------
-- The subset order on sets of traces.                                --
--                                                                    --
-- The subset grade orders `NeTraces` by `_⊑_` of `Sets`; below are   --
-- the reading of `_⊑_` as membership and the zero-product law of the --
-- grade.                                                             --
--                                                                    --
-- `_⊑_` is `liftˢ _≡_`, the set-level lift of the ordered trace      --
-- grades at the discrete order. The discrete order is not a          --
-- `TraceOrder`, which must supply `≼-nil : ε ≼ t`, and `ε ≡ t` does  --
-- not hold; the subset grade is therefore defined beside the lifted  --
-- family, not as an instance of it.                                  --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)

module Grades.Examples.Traces.Subsets.Base
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_) where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans

open WithDecEq _≟ₒ_ using (_⊑_; _∈?_; _≟ᵀ_)

------------------------------------------------------------------------
-- `_⊑_` is membership-wise inclusion
--
-- The lift wraps a decision in `True`, which makes the order
-- proof-irrelevant; these two unwrap it.

∈-⊑ : {xs ys : List Trace} {s : Trace} → xs ⊑ ys → s ∈ xs → s ∈ ys
∈-⊑ {xs} {s = s} sub mem = toWitness (sub s (fromWitness {a? = s ∈? xs} mem))

⊑-∈ : {xs ys : List Trace} → ((s : Trace) → s ∈ xs → s ∈ ys) → xs ⊑ ys
⊑-∈ f s m = fromWitness (f s (toWitness m))

------------------------------------------------------------------------
-- Zero-product, for a cap
--
-- A language product inside `{ ε }` has both factors inside it: each
-- member of a factor pairs with some member of the other, the pair is
-- the empty trace, and the trace monoid is conical.

⊑-zero-productˡ : {xs ys : List Trace} → NonEmpty ys
                → (xs ·ˢ ys) ⊑ traces 𝟏 → xs ⊑ traces 𝟏
⊑-zero-productˡ {xs} {ys} ne sub = ⊑-∈ step
  where
    step : (s : Trace) → s ∈ xs → s ∈ traces 𝟏
    step s s∈xs with neHead ys ne
    ... | y , y∈ys =
          here (∙-conicalˡ {s} {y}
                 (∈-[ε]⁻ (∈-⊑ sub (∈-cartesianProductWith⁺ _∙_ s∈xs y∈ys))))

⊑-zero-productʳ : {xs ys : List Trace} → NonEmpty xs
                → (xs ·ˢ ys) ⊑ traces 𝟏 → ys ⊑ traces 𝟏
⊑-zero-productʳ {xs} {ys} ne sub = ⊑-∈ step
  where
    step : (s : Trace) → s ∈ ys → s ∈ traces 𝟏
    step s s∈ys with neHead xs ne
    ... | x , x∈xs =
          here (∙-conicalʳ {x} {s}
                 (∈-[ε]⁻ (∈-⊑ sub (∈-cartesianProductWith⁺ _∙_ x∈xs s∈ys))))
