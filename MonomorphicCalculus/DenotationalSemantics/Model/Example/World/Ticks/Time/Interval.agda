-------------------------------------------------------------------------
-- A time-ticks Kripke frame for the time intervals with a             --
-- possibly-infinite right endpoint as the resource grades.            --
--                                                                     --
-- Worlds are time points `ℕ`. A resource grade `[ min , max ]` (with  --
-- `max : ℕ∞`) reaches exactly the worlds inside its window ahead; an  --
-- infinite `max` imposes no upper bound (`↑ w' ≤∞ ∞` always holds):   --
--                                                                     --
--   w ⊑[ i ] w'   iff   min i + w ≤ w'   and   ↑ w' ≤∞ (max i +∞ ↑ w) --
--                                                                     --
-- Multiplying grades (`·ᵢ`) adds the endpoints (with `∞` absorbing on --
-- the right), so composing two accessibilities advances into the      --
-- summed window.                                                      --
-------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.Interval where

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant;
         +-monoˡ-≤; +-monoʳ-≤; +-comm; +-assoc)
open import Data.Product using (_×_; _,_)

open import Grades.Examples.Time.Interval
  using (Interval∞; [_,_]; min; max; _·ᵢ_; _≾ᵢ_; interval;
         ℕ∞; ↑_; ∞; _+∞_; _≤∞_; +∞-mono-≤∞; ≤∞-refl; ≤∞-trans; ≤∞-irrelevant;
         +∞-assoc)

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.World

-- ℕ∞ helpers used to rearrange the window bounds

+∞-comm : ∀ a b → a +∞ b ≡ b +∞ a
+∞-comm (↑ m) (↑ n) = cong ↑_ (+-comm m n)
+∞-comm (↑ m) ∞     = refl
+∞-comm ∞     (↑ n) = refl
+∞-comm ∞     ∞     = refl

≤∞-reflexive : ∀ {a b} → a ≡ b → a ≤∞ b
≤∞-reflexive refl = ≤∞-refl

-- Accessibility on time ticks: reach exactly the worlds within the
-- window `[ min i , max i ]` ticks ahead (no upper bound when `max i` is
-- infinite).

_⊑ᵗ[_]_ : ℕ → Interval∞ → ℕ → Set
w ⊑ᵗ[ i ] w' = (min i + w ≤ w') × (↑ w' ≤∞ (max i +∞ ↑ w))

-- reflexivity at the unit grade `[ 0 , ↑ 0 ]` (the singleton window)

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ [ 0 , ↑ 0 ] ] w
⊑ᵗ-refl = ≤-refl , ≤-refl

-- transitivity multiplies the grades (adds both endpoints)

⊑ᵗ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ᵗ[ ρ₁ ] w' → w' ⊑ᵗ[ ρ₂ ] w'' → w ⊑ᵗ[ ρ₁ ·ᵢ ρ₂ ] w''
⊑ᵗ-trans {ρ₁} {ρ₂} {w} {w'} (loᵢ , hiᵢ) (loⱼ , hiⱼ) =
  ≤-trans (≤-reflexive (trans (cong (_+ w) (+-comm (min ρ₁) (min ρ₂)))
                              (+-assoc (min ρ₂) (min ρ₁) w)))
          (≤-trans (+-monoʳ-≤ (min ρ₂) loᵢ) loⱼ)
  ,
  ≤∞-trans hiⱼ
    (≤∞-trans (+∞-mono-≤∞ {max ρ₂} {↑ w'} {max ρ₂} {max ρ₁ +∞ ↑ w}
                          (≤∞-refl {max ρ₂}) hiᵢ)
              (≤∞-reflexive (trans (sym (+∞-assoc (max ρ₂) (max ρ₁) (↑ w)))
                                   (cong (_+∞ ↑ w) (+∞-comm (max ρ₂) (max ρ₁))))))

-- covariance: a wider window (a larger interval) gives a larger relation

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵢ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {ρ₁} {ρ₂} {w} (minrel , maxrel) (lo , hi) =
  ≤-trans (+-monoˡ-≤ w minrel) lo
  ,
  ≤∞-trans hi (+∞-mono-≤∞ {max ρ₁} {↑ w} {max ρ₂} {↑ w} maxrel (≤∞-refl {↑ w}))

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant (lo , hi) (lo' , hi') =
  cong₂ _,_ (≤-irrelevant lo lo') (≤∞-irrelevant hi hi')

-- The frame.

ticks : World interval
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
  }
