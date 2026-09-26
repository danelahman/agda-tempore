------------------------------------------------------------------------
-- The allowance cap does not project onto quotas.                    --
--                                                                    --
-- Going up the allowance order, an operation becomes a delay that    --
-- covers it: `⌈ o ⌉ ≼ᵃ ⟨ 1 + costʰⁱ o ⟩`. A pure delay draws on no   --
-- counter, so every grade morphism into at-most counts sends it to   --
-- the unit, which is the least quota. By monotonicity the bound      --
-- `⌈ o ⌉` is sent to the unit as well:                               --
--                                                                    --
--   map F (within ⟅ ⌈ o ⌉ ⟆)  ≡  uᵛ                                  --
--                                                                    --
-- for every morphism `F` and every operation `o`. No morphism        --
-- therefore counts what a bound permits: the quota it assigns to     --
-- `⌈ o ⌉` leaves nothing for `o` itself.                             --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ; _<_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Example.System.Counts.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o)
  {n : ℕ} (index : Op → Fin n) where

open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; any?)
open import Data.Nat.Base using (suc; _+_; _≤_)
open import Data.Nat.Properties using (n≤1+n; ≤-reflexive; ≤-trans)
open import Data.Vec.Base using (Vec; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades

open import Syntax.Grades.Traces.Allowance.Core Op costʰⁱ
  using (_≼ᵃ[_]_; nil; bank-delay; use-op)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (right-sided; within_; _≾_; singleton; of-nat; traces; _≽?_;
         Trace; ⌈_⌉; ⟨_⟩; ∣1+∣⁺)

open import Syntax.Grades.Example.Time.RightSided using (_≾ₒ_; uₒ-least)
open import Syntax.Grades.Example.Counts.AtMost
open import Syntax.Grades.Example.Counts.Occurrences Op index

------------------------------------------------------------------------
-- An operation is permitted by a delay that covers it

op≼delay : (o : Op) → ⌈ o ⌉ ≼ᵃ[ 0 ] ⟨ suc (costʰⁱ o) ⟩
op≼delay o =
  bank-delay (use-op (≤-trans (n≤1+n (costʰⁱ o)) (≤-reflexive (sym (∣1+∣⁺ (costʰⁱ o))))) nil)

op≾delay : (o : Op)
         → within singleton ⌈ o ⌉ ≾ Grade.of-nat right-sided (suc (costʰⁱ o))
op≾delay o p m with toWitness m
... | here refl =
  fromWitness {a? = any? (_≽?_ ⌈ o ⌉) (traces (of-nat (suc (costʰⁱ o))))}
              (here (op≼delay o))

------------------------------------------------------------------------
-- Every morphism into at-most counts forgets the operation

module _ (F : right-sided →ᵍ at-most-counts n) where

  open _→ᵍ_ F

  erases : (o : Op) → map (within singleton ⌈ o ⌉) ≡ uᵛ
  erases o =
    ≾ᵛ-antisym
      (≾ᵛ-trans (map-monotone (op≾delay o))
                (≾ᵛ-reflexive (map-of-nat {suc (costʰⁱ o)})))
      (uᵛ-least uₒ-least _)

  -- so the quota it gives `⌈ o ⌉` does not cover the run `⌈ o ⌉`

  miscounts : (o : Op)
            → ¬ (tabulate (λ i → upto (occ i ⌈ o ⌉)) ≾ᵛ map (within singleton ⌈ o ⌉))
  miscounts o rel =
    absurd (subst (λ h → h + 0 ≤ 0) (hit-index o)
             (subst₂ _≾ₒ_ (lookup∘tabulate (λ i → upto (occ i ⌈ o ⌉)) (index o))
                          (lookup-uᵛ (index o))
                          (≾ᵛ-lookup (subst (_ ≾ᵛ_) (erases o) rel) (index o))))
    where
      absurd : ¬ (1 + 0 ≤ 0)
      absurd ()
