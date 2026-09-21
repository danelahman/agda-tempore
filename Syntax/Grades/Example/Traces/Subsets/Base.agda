------------------------------------------------------------------------
-- What the subset preorder on sets of traces supplies.                --
--                                                                     --
-- The subset grade orders `NeTraces` by `Sets`' `_⊑_`, so what it     --
-- rests on is collected here: the reading of `_⊑_` as plain           --
-- membership, and the zero-product law its grade structure needs.     --
--                                                                     --
-- `_⊑_` is `liftˢ _≡_`: the same set-level lift the ordered trace     --
-- grades use, at the discrete order. That is also why it does not go  --
-- through `Traces.Order`/`Traces.OrderLift` -- a `TraceOrder` must    --
-- supply `≼-nil : ε ≼ t`, and `ε ≡ t` is false. So the subset grade   --
-- sits beside the lifted family rather than inside it.                --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Subsets.Base
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op

open WithDecEq _≟ₒ_ using (_⊑_; _∈?_; _≟ᵀ_)

------------------------------------------------------------------------
-- `_⊑_` is membership-wise inclusion
--
-- The lift's `True`-of-a-decision packaging is what makes the order
-- proof-irrelevant; these two turn it back into the statement it is.

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
                → (xs ·ˢ ys) ⊑ traces u → xs ⊑ traces u
⊑-zero-productˡ {xs} {ys} ne sub = ⊑-∈ step
  where
    step : (s : Trace) → s ∈ xs → s ∈ traces u
    step s s∈xs with neHead ys ne
    ... | y , y∈ys =
          here (∙-conicalˡ {s} {y}
                 (∈-[ε]⁻ (∈-⊑ sub (∈-cartesianProductWith⁺ _∙_ s∈xs y∈ys))))

⊑-zero-productʳ : {xs ys : List Trace} → NonEmpty xs
                → (xs ·ˢ ys) ⊑ traces u → ys ⊑ traces u
⊑-zero-productʳ {xs} {ys} ne sub = ⊑-∈ step
  where
    step : (s : Trace) → s ∈ ys → s ∈ traces u
    step s s∈ys with neHead xs ne
    ... | x , x∈xs =
          here (∙-conicalʳ {x} {s}
                 (∈-[ε]⁻ (∈-⊑ sub (∈-cartesianProductWith⁺ _∙_ x∈xs s∈ys))))
