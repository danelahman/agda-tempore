------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.     --
--                                                                    --
-- The effect grades are the rigid finite-expression intervals of     --
-- `Traces.TimedRegex.Finite.Interval`: a lower bound `L` and an      --
-- upper bound `U` that some run fits. The resource grades are the    --
-- intervals of dense time, each end open or closed. The projection   --
-- is the duration hull, read off each end                            --
-- (`Exact.Finite.Durations`):                                        --
--                                                                    --
--   ∣ [ L , U ] ∣ᵉ  =  ⟪ lower end of the hull of L ,                --
--                        upper end of the hull of U ⟫                --
--                                                                    --
-- The run both ends fit lasts a duration in both hulls, so the two   --
-- ends bound a non-empty interval. Ends keep their sides: `> 1` and  --
-- `< 3` give `] 1 , 3 [`. A delay of `q`, graded by `idle ≥ q` and   --
-- `idle ≤ q`, is measured `[ q , q ]`.                               --
--                                                                    --
-- The unit is measured `[ 0 , 0 ]`, as is `[ ≥ 0 , ε ]`, which is    --
-- not below the unit, so the projection does not reflect the order   --
-- there.                                                             --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.System.Traces.TimedRegex.Finite.Interval
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([])
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitnessFalse; fromWitness)

open import Grades.Base
open import Grades.Hints using (SystemHints; noGradeHints)
open import Grades.Durations.Monus ℚ≥0ᵀ using (Carrier; 0ᴰ; _<ᴰ_; _<ᴰ?_; ≮0⇒≡0)
open import Grades.Durations.Intervals ℚ≥0ᵀ
  using (Cut; Hi; fin; ⁻; ⁺; 0⁻; _⊑_; _⊑ʰ_; _◁_; _◁?_; ⊑-trans; 0⁻-least;
         ⊑-◁-trans; ◁-⊑ʰ-trans; ⊏-by-side; Interval; ⟪_,_⟫; lo; hi; eqⁱ; pointⁱ)
  renaming (_∣_ to _∣ᶜ_; ∞ to ∞ʰ)
open import Grades.Durations.Intervals.Dense ℚ≥0ᵀ using (⁺⋢⁻)
open import Util.NonNegativeRational using (#_; _≤?_)
open import Grades.Examples.Time.Rational.Interval
  using (rational-intervals; rational-intervalsʰ)

open import Grades.Examples.Traces.TimedRegex.Finite.Interval Op n code name name-code code-name running
  using (interval; Consistent)
open import Grades.Examples.Traces.TimedRegex.Finite.Base Op n code name name-code code-name running
  using (Proper′; ⌜_⌝; expr; ⟦_⟧; waitᴸ; waitᵁ; at-least′; lower; upper; str)
open import Data.Fin.Subset using () renaming (⊤ to all)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Grades.Exact.Finite.Durations ℚ≥0ᵀ Op n code code-injective name code-name
  running ℚ≥0-dense (# 1) one-pos
  using (hull-sound; upperʰ; hullᴾ; hullᴾ-≡; hullᴾ-is; hullᴾ-ε; hullᴾ-·; hullᴾ-∣; hullᴾ-mono; _∈ʰ_)
open import Grades.Exact.Order ℚ≥0ᵀ Op n code code-injective using (⊑-dur) renaming (_⊑_ to _⊑ʷ_)
open import Grades.Exact.Base ℚ≥0ᵀ Op n code code-injective using (dur)

------------------------------------------------------------------------
-- The ends of a consistent pair bound an interval

private
  -- the run's duration lies in each hull
  in-hull : ∀ {s} (c : Proper′ s) {x y} → ⟦ expr c ⟧ y → x ⊑ʷ y → dur x ∈ʰ just (hullᴾ c)
  in-hull c {x} {y} y∈ xy =
    subst (_∈ʰ just (hullᴾ c)) (sym (⊑-dur xy)) (subst (dur y ∈ʰ_) (hullᴾ-≡ c) (hull-sound (expr c) y∈))

  coherent : ∀ L U → Consistent (L , U) → lo (hullᴾ L) ◁ hi (hullᴾ U)
  coherent L U (x , (y , y∈ , xy) , (z , z∈ , xz)) =
    ⊑-◁-trans {lo (hullᴾ L)} {dur x ∣ᶜ ⁻} {hi (hullᴾ U)} (proj₁ (in-hull L y∈ xy))
      (◁-⊑ʰ-trans {dur x ∣ᶜ ⁻} {fin (dur x ∣ᶜ ⁺)} {hi (hullᴾ U)} (⊏-by-side refl)
        (proj₂ (in-hull U z∈ xz)))

------------------------------------------------------------------------
-- The projection

mapₒ : Grade.Carrier interval → Interval
mapₒ ((L , U) , c) = ⟪ lo (hullᴾ L) , hi (hullᴾ U) ⟫ {fromWitness (coherent L U c)}

private
  open Grade rational-intervals using (≃-reflexive) renaming (_≃_ to _≃ᵢ_)

  -- an interval is determined by its ends
  ends : ∀ (i j : Interval) → lo i ≡ lo j → hi i ≡ hi j → i ≃ᵢ j
  ends i j e e′ = ≃-reflexive (eqⁱ {i} {j} e e′)

  module E = Grade interval
  module R = Grade rational-intervals

  wait-lo : ∀ τ → lo (hullᴾ (waitᴸ τ)) ≡ τ ∣ᶜ ⁻
  wait-lo τ = case (0ᴰ <ᴰ? τ)
    where
      case : (d : Dec (0ᴰ <ᴰ τ)) → lo (hullᴾ (at-least′ τ d)) ≡ τ ∣ᶜ ⁻
      case (yes p) = cong lo (hullᴾ-is (at-least′ τ (yes p)) {⟪ τ ∣ᶜ ⁻ , ∞ʰ ⟫} refl)
      case (no ¬p) = trans (cong lo (hullᴾ-ε {lower})) (cong (_∣ᶜ ⁻) (sym (≮0⇒≡0 ¬p)))

  wait-hi : ∀ τ → hi (hullᴾ (waitᵁ τ)) ≡ fin (τ ∣ᶜ ⁺)
  wait-hi τ = case (0⁻ ◁? fin (τ ∣ᶜ ⁺)) (hullᴾ-≡ (waitᵁ τ))
    where
      case : (d : Dec (0⁻ ◁ fin (τ ∣ᶜ ⁺)))
           → upperʰ (fin (τ ∣ᶜ ⁺)) d ≡ just (hullᴾ (waitᵁ τ))
           → hi (hullᴾ (waitᵁ τ)) ≡ fin (τ ∣ᶜ ⁺)
      case (yes _) eq = cong hi (just-injective (sym eq))
      case (no ¬p) _  = ⊥-elim (¬p (λ r → ⁺⋢⁻ (⊑-trans r (0⁻-least (τ ∣ᶜ ⁻)))))

interval-runs→intervals : interval →ᵍ rational-intervals
interval-runs→intervals = record
  { map          = mapₒ
  ; map-monotone = λ {a} {b} (pL , pU) →
      proj₁ (hullᴾ-mono {c = proj₁ (proj₁ a)} {proj₁ (proj₁ b)} pL) ,
      proj₂ (hullᴾ-mono {c = proj₂ (proj₁ a)} {proj₂ (proj₁ b)} pU)
  ; map-𝟏        = ends (mapₒ E.𝟏) R.𝟏 (cong lo (hullᴾ-ε {lower})) (cong hi (hullᴾ-ε {upper}))
  ; map-·        = λ {a} {b} →
      ends (mapₒ (a E.· b)) (mapₒ a R.· mapₒ b) (cong lo (hullᴾ-· (proj₁ (proj₁ a)) (proj₁ (proj₁ b))))
           (cong hi (hullᴾ-· (proj₂ (proj₁ a)) (proj₂ (proj₁ b))))
  ; map-⊤        =
      ends (mapₒ E.⊤) R.⊤ (cong lo (hullᴾ-is (⌜ str all (0ᴰ ∣ᶜ ⁻) ⌝) {⟪ 0ᴰ ∣ᶜ ⁻ , ∞ʰ ⟫} refl))
           (cong hi (hullᴾ-is (⌜ str all ∞ʰ ⌝) {⟪ 0⁻ , ∞ʰ ⟫} refl))
  ; map-⊔        = λ {a} {b} →
      ends (mapₒ (a E.⊔ b)) (mapₒ a R.⊔ mapₒ b) (cong lo (hullᴾ-∣ (proj₁ (proj₁ a)) (proj₁ (proj₁ b))))
           (cong hi (hullᴾ-∣ (proj₂ (proj₁ a)) (proj₂ (proj₁ b))))
  ; map-ι        = λ {τ} → ends (mapₒ (E.ι τ)) (R.ι τ) (wait-lo τ) (wait-hi τ)
  }

intervalRunsToIntervalsGradeSystem : GradeSystem
intervalRunsToIntervalsGradeSystem = record
  { RGrade = rational-intervals
  ; EGrade = interval
  ; ∣-∣ᵉ   = interval-runs→intervals
  }

-- its hints

intervalRunsToIntervalsGradeSystemʰ : SystemHints intervalRunsToIntervalsGradeSystem
intervalRunsToIntervalsGradeSystemʰ = record
  { RHints      = rational-intervalsʰ
  ; EHints      = noGradeHints
  ; reflects-𝟏? = nothing
  ; witnesses   = λ _ _ _ → []
  }
