----------------------------------------------------------------------------
-- A time-ticks Kripke frame for the time intervals with a                --
-- possibly infinite right endpoint and a formal greatest grade.          --
--                                                                        --
-- Worlds are time points `ℕ`. A grade `window [ min , max ]` reaches     --
-- exactly the worlds inside its window ahead, as in the plain frame;     --
-- `no-window` bounds neither end and reaches every world ahead:          --
--                                                                        --
--   w ⊑[ window i ] w'   iff   min i + w ≤ w'  and                       --
--                              ↑ w' ≤∞ (max i +∞ ↑ w)                    --
--   w ⊑[ no-window ] w'  iff   w ≤ w'                                    --
--                                                                        --
-- The relation at `no-window` contains every other, as covariance        --
-- requires of the greatest grade, and is the greatest forward relation;  --
-- it is closed under composition, `no-window` being absorbing.           --
----------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.IntervalWithTop where

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant; m≤n+m;
         +-monoˡ-≤; +-monoʳ-≤; +-comm; +-assoc)
open import Data.Product using (_×_; _,_)

open import Grades.Examples.Time.Interval
  using (Interval∞; [_,_]; min; max;
         Interval∞⊤; window_; no-window; _·ʷ_; _≾ʷ_;
         intervals-with-⊤;
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
-- window `[ min i , max i ]` ticks ahead, and any world ahead at the
-- greatest grade.

_⊑ᵗ[_]_ : ℕ → Interval∞⊤ → ℕ → Set
w ⊑ᵗ[ window i ]  w' = (min i + w ≤ w') × (↑ w' ≤∞ (max i +∞ ↑ w))
w ⊑ᵗ[ no-window ] w' = w ≤ w'

-- every grade moves forward

⊑ᵗ-forward : ∀ ρ {w w'} → w ⊑ᵗ[ ρ ] w' → w ≤ w'
⊑ᵗ-forward (window i) {w} (lo , _) = ≤-trans (m≤n+m w (min i)) lo
⊑ᵗ-forward no-window      p        = p

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
⊑ᵗ-trans {window i}  {no-window} p q = ≤-trans (⊑ᵗ-forward (window i) p) q
⊑ᵗ-trans {no-window} {ρ₂}        p q = ≤-trans p (⊑ᵗ-forward ρ₂ q)

-- covariance: a wider window (a larger interval) gives a larger
-- relation, and `no-window` is above every grade

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ʷ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {window ρ₁} {window ρ₂} {w} (minrel , maxrel) (lo , hi) =
  ≤-trans (+-monoˡ-≤ w minrel) lo
  ,
  ≤∞-trans hi (+∞-mono-≤∞ {max ρ₁} {↑ w} {max ρ₂} {↑ w} maxrel (≤∞-refl {↑ w}))
⊑ᵗ-mono {window i}  {no-window} rel p = ⊑ᵗ-forward (window i) p
⊑ᵗ-mono {no-window} {window _}  ()
⊑ᵗ-mono {no-window} {no-window} rel p = p

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant {window _}  (lo , hi) (lo' , hi') =
  cong₂ _,_ (≤-irrelevant lo lo') (≤∞-irrelevant hi hi')
⊑ᵗ-irrelevant {no-window} p         q          = ≤-irrelevant p q

-- The frame.

ticks : World intervals-with-⊤
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
  }
