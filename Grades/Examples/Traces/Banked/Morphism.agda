------------------------------------------------------------------------
-- Grade morphisms between banked trace grades along a morphism of    --
-- durations.                                                         --
--                                                                    --
-- A morphism `h` of time domains that keeps positive durations       --
-- positive carries the banked trace grades at costs `c` to those at  --
-- costs `h ∘ c`: traces are mapped delay by delay (`Traces.Along`),  --
-- which is monotone for the coverage and allowance orders and scales --
-- durations by `h`, so the lifted grades are mapped by               --
-- `Lifted.Morphism`. At the inclusion of whole steps into rational   --
-- time this reads every trace grade over ℕ in rational time          --
-- (`Traces.Banked.Rational`).                                        --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)
open import Relation.Nullary using (¬_)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; _→ᴰ_)

module Grades.Examples.Traces.Banked.Morphism
  {D₁ D₂ : Duration} (T₁ : TimeDomain D₁) (T₂ : TimeDomain D₂)
  (h : D₁ →ᴰ D₂)
  (h-pos : (τ : Duration.Carrier D₁)
         → TimeDomain._≤ᴰ_ T₂ (_→ᴰ_.map h τ) (Duration.0ᴰ D₂)
         → TimeDomain._≤ᴰ_ T₁ τ (Duration.0ᴰ D₁))
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  where

import Grades.Durations.Monus as Monus
import Grades.Traces.Along as Along
import Grades.Traces.Coverage as Coverage
import Grades.Traces.Coverage.AsOrder as CoverageOrder
import Grades.Traces.Allowance as Allowance
import Grades.Traces.Allowance.AsOrder as AllowanceOrder
import Grades.Traces.RunConsistency as RC
import Grades.Examples.Traces.Lifted.Morphism as Morphism

open _→ᴰ_ h using () renaming (map to hᴰ)

private
  module M₁ = Monus T₁
  module M₂ = Monus T₂
  module A = Along T₁ T₂ h h-pos Op
  module L = Morphism T₁ T₂ h Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
               A.mapᵀ A.mapᵀ-∙ refl A.mapᵀ-⟨⟩

  -- a cost that is not zero stays not zero
  h-≢0 : ∀ {τ} → ¬ (τ ≡ M₁.0ᴰ) → ¬ (hᴰ τ ≡ M₂.0ᴰ)
  h-≢0 ne e = ne (M₁.≤0⇒≡0 (h-pos _ (M₂.≤ᴰ-reflexive e)))

------------------------------------------------------------------------
-- Guarantees: `LowerBound.lower-bound→`, from the grade at costs
-- `costˡᵒ` to the grade at costs `h ∘ costˡᵒ`

module LowerBound (costˡᵒ : Op → Duration.Carrier D₁) =
  L.LowerBound
    (CoverageOrder.coverageOrder T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ)
    (CoverageOrder.coverageOrder T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans (λ o → hᴰ (costˡᵒ o)))
    (A.Coverage.mapᵀ-≼ᶜ₀ costˡᵒ)

------------------------------------------------------------------------
-- Allowances: `UpperBound.upper-bound→`

module UpperBound (costʰⁱ : Op → Duration.Carrier D₁)
  (costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ Duration.0ᴰ D₁)) =
  L.UpperBound
    (AllowanceOrder.allowanceOrder T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos)
    (AllowanceOrder.allowanceOrder T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans (λ o → hᴰ (costʰⁱ o))
       (λ o → h-≢0 (costʰⁱ-pos o)))
    (A.Allowance.mapᵀ-≼ᵃ₀ costʰⁱ)

------------------------------------------------------------------------
-- Intervals: `Interval.interval→`

module Interval (costˡᵒ costʰⁱ : Op → Duration.Carrier D₁)
  (cost-≤ : (o : Op) → TimeDomain._≤ᴰ_ T₁ (costˡᵒ o) (costʰⁱ o))
  (costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ Duration.0ᴰ D₁)) =
  L.Interval
    costˡᵒ costʰⁱ cost-≤ (λ o → hᴰ (costˡᵒ o)) (λ o → hᴰ (costʰⁱ o))
    (λ o → A.h-mono (cost-≤ o))
    (CoverageOrder.coverageOrder T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ)
    (AllowanceOrder.allowanceOrder T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos)
    (CoverageOrder.coverageOrder T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans (λ o → hᴰ (costˡᵒ o)))
    (AllowanceOrder.allowanceOrder T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans (λ o → hᴰ (costʰⁱ o))
       (λ o → h-≢0 (costʰⁱ-pos o)))
    (Coverage.duration-≼ᶜ T₁ Op costˡᵒ)
    (Allowance.duration-≼ᵃ T₁ Op costʰⁱ)
    (Coverage.duration-≼ᶜ T₂ Op (λ o → hᴰ (costˡᵒ o)))
    (Allowance.duration-≼ᵃ T₂ Op (λ o → hᴰ (costʰⁱ o)))
    (A.Coverage.mapᵀ-≼ᶜ₀ costˡᵒ)
    (A.Allowance.mapᵀ-≼ᵃ₀ costʰⁱ)
    (RC.DecConsistency._⋈?_ T₁ Op costˡᵒ costʰⁱ cost-≤ _≟ₒ_)
    (RC.DecConsistency._⋈?_ T₂ Op (λ o → hᴰ (costˡᵒ o)) (λ o → hᴰ (costʰⁱ o))
       (λ o → A.h-mono (cost-≤ o)) _≟ₒ_)
