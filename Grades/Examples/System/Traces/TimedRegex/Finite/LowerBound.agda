------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.     --
--                                                                    --
-- The effect grades are the rigid finite-expression lower bounds of  --
-- `Traces.TimedRegex.Finite.LowerBound`; the resource grades are the --
-- lower bounds on dense time, "at least `q` time units".             --
-- The projection measures a grade by the infimum of the durations of --
-- its runs, the lower end of its duration hull                       --
-- (`Exact.Finite.Durations`):                                        --
--                                                                    --
--   ∣ L ∣ᵉ  =  [ inf { dur x ∣ x a run of L } ,+∞⟩                   --
--                                                                    --
-- The resource intervals have closed ends, so an open end of the     --
-- hull is closed: `> 1` and `≥ 1` both measure `[ 1 ,+∞⟩`.           --
--                                                                    --
-- A delay of `q` is graded by `idle ≥ q`, measured `[ q ,+∞⟩`; `≥ 0` --
-- measures `[ 0 ,+∞⟩`, the greatest resource grade, which is also    --
-- the unit, so the projection does not reflect the order there.      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.System.Traces.TimedRegex.Finite.LowerBound
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.List.Base using ([])
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Grades.Base
open import Grades.Hints using (SystemHints; noGradeHints)
open import Grades.Durations.Monus ℚ≥0ᵀ using (Carrier; 0ᴰ; _<ᴰ_; _<ᴰ?_; ≮0⇒≡0)
open import Grades.Durations.Intervals ℚ≥0ᵀ
  using (Cut; pt; ⁻; _⊑_; ⊑⇒≤; _⊓ᶜ_; ⊓ᶜ-sel; ⊓ᶜ-lbˡ; ⊓ᶜ-lbʳ; _+ˡ_; lo; ⟪_,_⟫)
  renaming (_∣_ to _∣ᶜ_; ∞ to ∞ʰ)
open import Grades.Examples.Time.Rational.LowerBound
  using (#_; _≤_; _≤?_; ≤-refl; _⊓_; ⊓-lbˡ; ⊓-lbʳ; ⊓-glb;
         𝕀; [_,+∞⟩; rational-lower-bounds; rational-lower-boundsʰ)

open import Grades.Examples.Traces.TimedRegex.Finite.LowerBound Op n code name name-code code-name running
  using (lower-bound; Proper′; ⌜_⌝; expr; εᵉ; at-least′; waitᴸ; lower; str)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Grades.Exact.Finite.Durations ℚ≥0ᵀ Op n code code-injective name code-name
  running ℚ≥0-dense (# 1) one-pos
  using (hullᴾ; hullᴾ-is; hullᴾ-ε; hullᴾ-·; hullᴾ-∣; hullᴾ-mono)

------------------------------------------------------------------------
-- The infimum of a lower end, against the order of its interval

private
  ⊓-pt : ∀ c c′ → pt (c ⊓ᶜ c′) ≤ pt c ⊓ pt c′
  ⊓-pt c c′ = ⊓-glb (⊑⇒≤ (⊓ᶜ-lbˡ c c′)) (⊑⇒≤ (⊓ᶜ-lbʳ c c′))

  pt-⊓ : ∀ c c′ → pt c ⊓ pt c′ ≤ pt (c ⊓ᶜ c′)
  pt-⊓ c c′ with ⊓ᶜ-sel c c′
  ... | inj₁ e rewrite e = ⊓-lbˡ (pt c) (pt c′)
  ... | inj₂ e rewrite e = ⊓-lbʳ (pt c) (pt c′)

  ≃-of : ∀ {p q} → p ≡ q → (q ≤ p) × (p ≤ q)
  ≃-of refl = ≤-refl , ≤-refl

------------------------------------------------------------------------
-- The projection: the infimum of the durations of the runs

mapₒ : Proper′ lower → 𝕀
mapₒ c = [ pt (lo (hullᴾ c)) ,+∞⟩

private
  -- the hull of a wait of at least `τ` starts at `τ`
  wait-lo : ∀ τ → pt (lo (hullᴾ (waitᴸ τ))) ≡ τ
  wait-lo τ = case (0ᴰ <ᴰ? τ)
    where
      case : (d : Dec (0ᴰ <ᴰ τ)) → pt (lo (hullᴾ (at-least′ τ d))) ≡ τ
      case (yes p) = cong (λ i → pt (lo i)) (hullᴾ-is (at-least′ τ (yes p)) {⟪ τ ∣ᶜ ⁻ , ∞ʰ ⟫} refl)
      case (no ¬p) = trans (cong (λ i → pt (lo i)) (hullᴾ-ε {lower})) (sym (≮0⇒≡0 ¬p))

lower-runs→lower-bounds : lower-bound →ᵍ rational-lower-bounds
lower-runs→lower-bounds = record
  { map          = mapₒ
  ; map-monotone = λ {c} {d} p → ⊑⇒≤ (proj₁ (hullᴾ-mono {c = c} {d} p))
  ; map-𝟏        = ≃-of (cong (λ i → pt (lo i)) (hullᴾ-ε {lower}))
  ; map-·        = λ {c} {d} → ≃-of (cong (λ i → pt (lo i)) (hullᴾ-· c d))
  ; map-⊤        = ≃-of (cong (λ i → pt (lo i)) (hullᴾ-is (⌜ str all (0ᴰ ∣ᶜ ⁻) ⌝) {⟪ 0ᴰ ∣ᶜ ⁻ , ∞ʰ ⟫} refl))
  ; map-⊔        = λ {c} {d} →
      subst (λ i → (pt (lo (hullᴾ c)) ⊓ pt (lo (hullᴾ d)) ≤ pt (lo i)) × (pt (lo i) ≤ pt (lo (hullᴾ c)) ⊓ pt (lo (hullᴾ d))))
            (sym (hullᴾ-∣ c d))
            (pt-⊓ (lo (hullᴾ c)) (lo (hullᴾ d)) , ⊓-pt (lo (hullᴾ c)) (lo (hullᴾ d)))
  ; map-ι        = λ {τ} → ≃-of (wait-lo τ)
  }

lowerRunsToLowerBoundsGradeSystem : GradeSystem
lowerRunsToLowerBoundsGradeSystem = record
  { RGrade = rational-lower-bounds
  ; EGrade = lower-bound
  ; ∣-∣ᵉ   = lower-runs→lower-bounds
  }

-- its hints

lowerRunsToLowerBoundsGradeSystemʰ : SystemHints lowerRunsToLowerBoundsGradeSystem
lowerRunsToLowerBoundsGradeSystemʰ = record
  { RHints      = rational-lower-boundsʰ
  ; EHints      = noGradeHints
  ; reflects-𝟏? = nothing
  ; witnesses   = λ _ _ _ → []
  }
