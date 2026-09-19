------------------------------------------------------------------------
-- A time-ticks Kripke frame for the left-sided time intervals with a   --
-- formal greatest grade as the resource grades.                        --
--                                                                    --
-- Worlds are time points `ℕ`. A grade `timed [ n ,+∞⟩` reaches every    --
-- world at least `n` ticks ahead, exactly as in the plain left-sided    --
-- frame; `untimed` claims no lower bound at all and so reaches every    --
-- world:                                                               --
--                                                                    --
--   w ⊑[ timed [ n ,+∞⟩ ] w'   iff   n + w ≤ w'                        --
--   w ⊑[ untimed ] w'          always                                  --
--                                                                    --
-- The total relation at `untimed` is forced by covariance, every grade  --
-- being below it, and composition survives because `untimed` absorbs.   --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSidedWithTop where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant;
         +-monoˡ-≤; +-monoʳ-≤; +-comm; +-assoc)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades.Example.Time.LeftSided
  using (𝕀⊤; timed_; untimed; [_,+∞⟩; _·ᵗ_; _≾ᵗ_;
         left-sided-intervals-with-⊤)

open import Util.Equality

open import DenotationalSemantics.Model.World

-- Accessibility on time ticks: reach any world at least `n` ticks ahead,
-- and any world at all at the greatest grade.

_⊑ᵗ[_]_ : ℕ → 𝕀⊤ → ℕ → Set
w ⊑ᵗ[ timed [ n ,+∞⟩ ] w' = n + w ≤ w'
w ⊑ᵗ[ untimed ]        w' = ⊤

-- reflexivity at the unit grade `timed [ 0 ,+∞⟩`

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ timed [ 0 ,+∞⟩ ] w
⊑ᵗ-refl = ≤-refl

-- transitivity multiplies the grades (adds the lower bounds); a product
-- with `untimed` is `untimed`

⊑ᵗ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ᵗ[ ρ₁ ] w' → w' ⊑ᵗ[ ρ₂ ] w'' → w ⊑ᵗ[ ρ₁ ·ᵗ ρ₂ ] w''
⊑ᵗ-trans {timed [ m ,+∞⟩} {timed [ n ,+∞⟩} {w} p q =
  ≤-trans (≤-reflexive (trans (cong (_+ w) (+-comm m n)) (+-assoc n m w)))
          (≤-trans (+-monoʳ-≤ n p) q)
⊑ᵗ-trans {timed _}        {untimed}        p q = tt
⊑ᵗ-trans {untimed}        {_}              p q = tt

-- covariance: a smaller lower bound (a larger interval) gives a larger
-- relation, and `untimed` is above every grade

⊑ᵗ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵗ ρ₂ → w ⊑ᵗ[ ρ₁ ] w' → w ⊑ᵗ[ ρ₂ ] w'
⊑ᵗ-mono {timed [ m ,+∞⟩} {timed [ n ,+∞⟩} {w} rel p = ≤-trans (+-monoˡ-≤ w rel) p
⊑ᵗ-mono {timed _}        {untimed}        rel p = tt
⊑ᵗ-mono {untimed}        {timed _}        ()
⊑ᵗ-mono {untimed}        {untimed}        rel p = tt

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ᵗ[ ρ ] w') → p ≡ q
⊑ᵗ-irrelevant {timed [ _ ,+∞⟩} p  q  = ≤-irrelevant p q
⊑ᵗ-irrelevant {untimed}        tt tt = refl

-- The frame.

ticks : World left-sided-intervals-with-⊤
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
  }
