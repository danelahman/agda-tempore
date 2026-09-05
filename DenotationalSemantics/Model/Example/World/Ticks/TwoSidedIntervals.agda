------------------------------------------------------------------------
-- A time-ticks Kripke frame for the two-sided time intervals as the    --
-- resource grades.                                                     --
--                                                                    --
-- Worlds are time points `ℕ`. A two-sided resource grade `[ min , max ]`--
-- ("between `min` and `max` ticks") reaches exactly the worlds inside    --
-- that window ahead:                                                    --
--                                                                    --
--   w ⊑[ i ] w'   iff   min i + w ≤ w'   and   w' ≤ max i + w          --
--                                                                    --
-- Multiplying grades (`·ᵢ`) adds the two endpoints, so composing two    --
-- accessibilities advances the world into the summed window.            --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.TwoSidedIntervals where

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant;
         +-monoˡ-≤; +-monoʳ-≤; +-comm; +-assoc)
open import Data.Product using (_×_; _,_)

open import Syntax.Grades.Example.Interval.TwoSided
  using (Interval; [_,_,_]; min; max; _·ᵢ_; _≾ᵢ_; two-sided-intervals)

open import Util.Equality

open import DenotationalSemantics.Model.World

-- Accessibility on time ticks: reach exactly the worlds within the
-- window `[ min i , max i ]` ticks ahead.

_⊑ᵗ[_]_ : ℕ → Interval → ℕ → Set
w ⊑ᵗ[ i ] w' = (min i + w ≤ w') × (w' ≤ max i + w)

-- reflexivity at the unit grade `[ 0 , 0 ]` (the singleton window)

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ [ 0 , 0 , z≤n ] ] w
⊑ᵗ-refl = ≤-refl , ≤-refl

-- transitivity multiplies the grades (adds both endpoints)

⊑ᵗ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ᵗ[ ρ₁ ] w' → w' ⊑ᵗ[ ρ₂ ] w'' → w ⊑ᵗ[ ρ₁ ·ᵢ ρ₂ ] w''
⊑ᵗ-trans {ρ₁} {ρ₂} {w} (pₗ , pᵤ) (qₗ , qᵤ) =
  ≤-trans (≤-reflexive (trans (cong (_+ w) (+-comm (min ρ₁) (min ρ₂)))
                              (+-assoc (min ρ₂) (min ρ₁) w)))
          (≤-trans (+-monoʳ-≤ (min ρ₂) pₗ) qₗ)
  ,
  ≤-trans (≤-trans qᵤ (+-monoʳ-≤ (max ρ₂) pᵤ))
          (≤-reflexive (trans (sym (+-assoc (max ρ₂) (max ρ₁) w))
                              (cong (_+ w) (+-comm (max ρ₂) (max ρ₁)))))

-- covariance: a wider window (a larger interval) gives a larger relation

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵢ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {ρ₁} {ρ₂} {w} (minrel , maxrel) (pₗ , pᵤ) =
  ≤-trans (+-monoˡ-≤ w minrel) pₗ
  ,
  ≤-trans pᵤ (+-monoˡ-≤ w maxrel)

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant (p₁ , p₂) (q₁ , q₂) =
  cong₂ _,_ (≤-irrelevant p₁ q₁) (≤-irrelevant p₂ q₂)

-- The frame.

ticks : World two-sided-intervals
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
  }
