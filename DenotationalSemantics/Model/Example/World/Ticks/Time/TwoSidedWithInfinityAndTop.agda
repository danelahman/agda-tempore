------------------------------------------------------------------------
-- A time-ticks Kripke frame for the two-sided time intervals with a    --
-- possibly-infinite right endpoint and a formal greatest grade.        --
--                                                                    --
-- Worlds are time points `ℕ`. A grade `window [ min , max ]` reaches     --
-- exactly the worlds inside its window ahead, exactly as in the plain    --
-- frame; `no-window` bounds neither end and so reaches every world:      --
--                                                                    --
--   w ⊑[ window i ] w'  iff  min i + w ≤ w'  and  ↑ w' ≤∞ (max i +∞ ↑ w) --
--   w ⊑[ no-window ] w'  always                                         --
--                                                                    --
-- The total relation at `no-window` is forced by covariance, every       --
-- grade being below it, and composition survives because `no-window`     --
-- absorbs.                                                              --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.Time.TwoSidedWithInfinityAndTop where

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant;
         +-monoˡ-≤; +-monoʳ-≤; +-comm; +-assoc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_]; min; max;
         Interval∞⊤; window_; no-window; _·ʷ_; _≾ʷ_;
         two-sided-intervals-with-⊤;
         ℕ∞; ↑_; ∞; _+∞_; _≤∞_; +∞-mono-≤∞; ≤∞-refl; ≤∞-trans; ≤∞-irrelevant;
         +∞-assoc)

open import Util.Equality

open import DenotationalSemantics.Model.World

-- ℕ∞ helpers used to rearrange the window bounds

+∞-comm : ∀ a b → a +∞ b ≡ b +∞ a
+∞-comm (↑ m) (↑ n) = cong ↑_ (+-comm m n)
+∞-comm (↑ m) ∞     = refl
+∞-comm ∞     (↑ n) = refl
+∞-comm ∞     ∞     = refl

≤∞-reflexive : ∀ {a b} → a ≡ b → a ≤∞ b
≤∞-reflexive refl = ≤∞-refl

-- Accessibility on time ticks: reach exactly the worlds within the
-- window `[ min i , max i ]` ticks ahead, and any world at all at the
-- greatest grade.

_⊑ᵗ[_]_ : ℕ → Interval∞⊤ → ℕ → Set
w ⊑ᵗ[ window i ]  w' = (min i + w ≤ w') × (↑ w' ≤∞ (max i +∞ ↑ w))
w ⊑ᵗ[ no-window ] w' = ⊤

-- reflexivity at the unit grade `window [ 0 , ↑ 0 ]` (the singleton
-- window)

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ window [ 0 , ↑ 0 ] ] w
⊑ᵗ-refl = ≤-refl , ≤-refl

-- transitivity multiplies the grades (adds both endpoints); a product
-- with `no-window` is `no-window`

⊑ᵗ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ᵗ[ ρ₁ ] w' → w' ⊑ᵗ[ ρ₂ ] w'' → w ⊑ᵗ[ ρ₁ ·ʷ ρ₂ ] w''
⊑ᵗ-trans {window ρ₁} {window ρ₂} {w} {w'} (loᵢ , hiᵢ) (loⱼ , hiⱼ) =
  ≤-trans (≤-reflexive (trans (cong (_+ w) (+-comm (min ρ₁) (min ρ₂)))
                              (+-assoc (min ρ₂) (min ρ₁) w)))
          (≤-trans (+-monoʳ-≤ (min ρ₂) loᵢ) loⱼ)
  ,
  ≤∞-trans hiⱼ
    (≤∞-trans (+∞-mono-≤∞ {max ρ₂} {↑ w'} {max ρ₂} {max ρ₁ +∞ ↑ w}
                          (≤∞-refl {max ρ₂}) hiᵢ)
              (≤∞-reflexive (trans (sym (+∞-assoc (max ρ₂) (max ρ₁) (↑ w)))
                                   (cong (_+∞ ↑ w) (+∞-comm (max ρ₂) (max ρ₁))))))
⊑ᵗ-trans {window _}  {no-window} p q = tt
⊑ᵗ-trans {no-window} {_}         p q = tt

-- covariance: a wider window (a larger interval) gives a larger
-- relation, and `no-window` is above every grade

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ʷ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {window ρ₁} {window ρ₂} {w} (minrel , maxrel) (lo , hi) =
  ≤-trans (+-monoˡ-≤ w minrel) lo
  ,
  ≤∞-trans hi (+∞-mono-≤∞ {max ρ₁} {↑ w} {max ρ₂} {↑ w} maxrel (≤∞-refl {↑ w}))
⊑ᵗ-mono {window _}  {no-window} rel p = tt
⊑ᵗ-mono {no-window} {window _}  ()
⊑ᵗ-mono {no-window} {no-window} rel p = tt

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant {window _}  (lo , hi) (lo' , hi') =
  cong₂ _,_ (≤-irrelevant lo lo') (≤∞-irrelevant hi hi')
⊑ᵗ-irrelevant {no-window} tt        tt         = refl

-- The frame.

ticks : World two-sided-intervals-with-⊤
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
  }
