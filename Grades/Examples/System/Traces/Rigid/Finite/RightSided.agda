------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.     --
--                                                                    --
-- The effect grades are the rigid finite-expression upper bounds of  --
-- `Traces.Rigid.Finite.RightSided`; the resource grades are the      --
-- right-sided intervals of dense time, "at most `q` time units".     --
-- The projection measures a grade by the supremum of the durations   --
-- of its runs, the upper end of its duration hull                    --
-- (`Exact.Finite.Durations`):                                        --
--                                                                    --
--   ∣ U ∣ᵉ  =  [0, sup { dur x ∣ x a run of U } ]                    --
--                                                                    --
-- The resource intervals have closed ends, so an open end of the     --
-- hull is closed: `< 1` and `≤ 1` both measure `[0, ↑ 1 ]`.          --
--                                                                    --
-- A delay of `q` is graded by `idle ≤ q`, measured `[0, ↑ q ]`; `≤∞` --
-- measures `[0, ∞ ]`. A grade measured `[0, ↑ 0 ]` has only runs of  --
-- no duration, the empty run, so the projection reflects the order   --
-- at the unit.                                                       --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.System.Traces.Rigid.Finite.RightSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitnessFalse; fromWitness)

open import Grades.Base
open import Grades.Hints using (SystemHints; noGradeHints)
open import Grades.Durations.Monus ℚ≥0ᵀ using (0ᴰ; _<ᴰ_)
open import Grades.Durations.Intervals ℚ≥0ᵀ
  using (Hi; fin; Cut; pt; _⊑ʰ_; ⁻; ⁺; 0⁻; _◁_; _◁?_; 0⁻-least; ⊑-trans; ⊑⇒≤;
         _⊔ʰ_; ⊔ʰ-sel; ⊔ʰ-ubˡ; ⊔ʰ-ubʳ; _+ʰ_; Interval; ⟪_,_⟫; hi; _⊆ⁱ_)
  renaming (_∣_ to _∣ᶜ_; ∞ to ∞ʰ)
open import Grades.Durations.Intervals.Dense ℚ≥0ᵀ using (⁺⋢⁻)
open import Util.NonNegativeRational using (#_; _≤_; _≤?_; ≤-trans)
open import Grades.Examples.Time.Dense.RightSided
  using (ℚ∞; ↑_; ∞; _≤∞_; ≤∞-refl; _+∞_; _⊔∞_; ⊔∞-ubˡ; ⊔∞-ubʳ; ⊔∞-lub;
         𝕀ᵣ; [0,_]; _≾ₒ_; uₒ; dense-right-sided-intervals; dense-right-sided-intervalsʰ)

open import Grades.Examples.Traces.Rigid.Finite.RightSided Op n code name name-code code-name running
  using (right-sided; Proper′; ⌜_⌝; expr; _≾ᴳ_; decided; εᵉ; waitᵁ; _≾ᵉ_; _≾ᵉ?_; ⟦_⟧; upper; str)
open import Data.Fin.Subset using () renaming (⊤ to all)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Grades.Exact.Finite.Durations ℚ≥0ᵀ Op n code code-injective name code-name
  running ℚ≥0-dense (# 1) one-pos
  using (hull; hull-sound; upperʰ; hullᴾ; hullᴾ-≡; hullᴾ-is; hullᴾ-ε; hullᴾ-·; hullᴾ-∣; hullᴾ-mono;
         _∈ʰ_)
open import Grades.Exact.Order ℚ≥0ᵀ Op n code code-injective using (⊑-refl)
open import Grades.Exact.Base ℚ≥0ᵀ Op n code code-injective using (dur; dur-pos)

------------------------------------------------------------------------
-- The supremum of an upper end

supʰ : Hi → ℚ∞
supʰ (fin c) = ↑ pt c
supʰ ∞ʰ      = ∞

supʰ-mono : ∀ {h h′} → h ⊑ʰ h′ → supʰ h ≤∞ supʰ h′
supʰ-mono {fin _} {fin _} r = ⊑⇒≤ r
supʰ-mono {fin _} {∞ʰ}    _ = _
supʰ-mono {∞ʰ}    {∞ʰ}    _ = _

supʰ-+ : ∀ h h′ → supʰ (h +ʰ h′) ≡ supʰ h +∞ supʰ h′
supʰ-+ (fin (_ ∣ᶜ _)) (fin (_ ∣ᶜ _)) = refl
supʰ-+ (fin (_ ∣ᶜ _)) ∞ʰ             = refl
supʰ-+ ∞ʰ             _              = refl

supʰ-⊔ : ∀ h h′ → supʰ (h ⊔ʰ h′) ≤∞ supʰ h ⊔∞ supʰ h′
supʰ-⊔ h h′ with ⊔ʰ-sel h h′
... | inj₁ e rewrite e = ⊔∞-ubˡ (supʰ h) (supʰ h′)
... | inj₂ e rewrite e = ⊔∞-ubʳ (supʰ h) (supʰ h′)

⊔-supʰ : ∀ h h′ → supʰ h ⊔∞ supʰ h′ ≤∞ supʰ (h ⊔ʰ h′)
⊔-supʰ h h′ = ⊔∞-lub {supʰ h} {supʰ h′} (supʰ-mono {h} (⊔ʰ-ubˡ h h′)) (supʰ-mono {h′} (⊔ʰ-ubʳ h h′))

------------------------------------------------------------------------
-- The projection: the supremum of the durations of the runs

mapₒ : Proper′ upper → 𝕀ᵣ
mapₒ c = [0, supʰ (hi (hullᴾ c)) ]

private
  -- the hull of a wait of at most `τ` reaches up to `τ`
  wait-hi : ∀ τ → hi (hullᴾ (waitᵁ τ)) ≡ fin (τ ∣ᶜ ⁺)
  wait-hi τ = case (0⁻ ◁? fin (τ ∣ᶜ ⁺)) (hullᴾ-≡ (waitᵁ τ))
    where
      case : (d : Dec (0⁻ ◁ fin (τ ∣ᶜ ⁺)))
           → upperʰ (fin (τ ∣ᶜ ⁺)) d ≡ just (hullᴾ (waitᵁ τ))
           → hi (hullᴾ (waitᵁ τ)) ≡ fin (τ ∣ᶜ ⁺)
      case (yes _) eq = cong hi (just-injective (sym eq))
      case (no ¬p) _  = ⊥-elim (¬p (λ r → ⁺⋢⁻ (⊑-trans r (0⁻-least (τ ∣ᶜ ⁻)))))

  -- the order is that of the suprema
  supᴾ-mono : ∀ {c d : Proper′ upper} → c ≾ᴳ d → supʰ (hi (hullᴾ c)) ≤∞ supʰ (hi (hullᴾ d))
  supᴾ-mono {c} {d} p = supʰ-mono {hi (hullᴾ c)} {hi (hullᴾ d)} (proj₂ (hullᴾ-mono {c = c} {d} p))

  ≃-of : ∀ {a b} → a ≡ b → (a ≤∞ b) Data.Product.× (b ≤∞ a)
  ≃-of {a} refl = ≤∞-refl {a} , ≤∞-refl {a}

upper-runs→right-sided-intervals : right-sided →ᵍ dense-right-sided-intervals
upper-runs→right-sided-intervals = record
  { map          = mapₒ
  ; map-monotone = λ {c} {d} → supᴾ-mono {c} {d}
  ; map-u        = ≃-of (cong (λ i → supʰ (hi i)) (hullᴾ-ε {upper}))
  ; map-·        = λ {c} {d} →
      ≃-of (trans (cong (λ i → supʰ (hi i)) (hullᴾ-· c d)) (supʰ-+ (hi (hullᴾ c)) (hi (hullᴾ d))))
  ; map-⊤        = ≃-of (cong (λ i → supʰ (hi i)) (hullᴾ-is ⌜ str all ∞ʰ ⌝ {⟪ 0⁻ , ∞ʰ ⟫} refl))
  ; map-⊔        = λ {c} {d} →
      subst (λ i → (supʰ (hi i) ≤∞ supʰ (hi (hullᴾ c)) ⊔∞ supʰ (hi (hullᴾ d)))
                   Data.Product.× (supʰ (hi (hullᴾ c)) ⊔∞ supʰ (hi (hullᴾ d)) ≤∞ supʰ (hi i)))
            (sym (hullᴾ-∣ c d))
        (supʰ-⊔ (hi (hullᴾ c)) (hi (hullᴾ d)) , ⊔-supʰ (hi (hullᴾ c)) (hi (hullᴾ d)))
  ; map-of-dur   = λ {τ} → ≃-of (cong supʰ (wait-hi τ))
  }

------------------------------------------------------------------------
-- A grade measured by no time has only the empty run

private
  -- for a general `d`, so that the decider is never unfolded at `εᵉ`
  lift : (c d : Proper′ upper) → c ≾ᵉ d → c ≾ᴳ d
  lift c d p = decided (fromWitness {a? = c ≾ᵉ? d} p)

  reflects : (c : Proper′ upper) → mapₒ c ≾ₒ uₒ → c ≾ᴳ εᵉ
  reflects c le = lift c εᵉ into
    where
      dur≤0 : ∀ {x} → ⟦ expr c ⟧ x → dur x ≤ # 0
      dur≤0 {x} x∈ = go (hi (hullᴾ c)) refl le
        where
          t∈ = subst (dur x ∈ʰ_) (hullᴾ-≡ c) (hull-sound (expr c) x∈)
          go : ∀ h → h ≡ hi (hullᴾ c) → supʰ h ≤∞ ↑ # 0 → dur x ≤ # 0
          go (fin c′) e s = ≤-trans (⊑⇒≤ (subst (fin (dur x ∣ᶜ ⁺) ⊑ʰ_) (sym e) (proj₂ t∈))) s
          go ∞ʰ       _ ()
      into : ∀ x → ⟦ expr c ⟧ x → _
      into []      x∈ = [] , refl , ⊑-refl
      into (i ∷ w) x∈ = ⊥-elim (dur-pos i w (dur≤0 x∈))

upperRunsToRightSidedIntervalsGradeSystem : GradeSystem
upperRunsToRightSidedIntervalsGradeSystem = record
  { RGrade = dense-right-sided-intervals
  ; EGrade = right-sided
  ; ∣_∣ᵉ   = upper-runs→right-sided-intervals
  }

-- its hints: the projection reflects the order at the unit

upperRunsToRightSidedIntervalsGradeSystemʰ : SystemHints upperRunsToRightSidedIntervalsGradeSystem
upperRunsToRightSidedIntervalsGradeSystemʰ = record
  { RHints      = dense-right-sided-intervalsʰ
  ; EHints      = noGradeHints
  ; reflects-u? = just reflects
  ; witnesses   = λ _ _ _ → []
  }
