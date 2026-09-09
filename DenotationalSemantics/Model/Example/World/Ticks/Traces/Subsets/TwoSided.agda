------------------------------------------------------------------------
-- A time-ticks Kripke frame for the two-sided subset intervals.       --
--                                                                    --
-- Worlds are time points `ℕ`, and a grade `[ P , Q ]` fences the      --
-- advance in from both sides:                                        --
--                                                                    --
--   w ⊑ᵗ[ [ P , Q ] ] w'   iff   w + duration p ≤ w'  for *all* p ∈ P --
--                          and   w' ≤ w + duration q  for *some* q ∈ Q --
--                                                                    --
-- The two quantifiers differ because the two endpoints weaken in      --
-- opposite directions of inclusion: below, weakening drops members,   --
-- so the condition must be asked of all of them; above, weakening     --
-- adds members, so one is enough.                                    --
--                                                                    --
-- Each half is the corresponding one-sided frame, and every frame     --
-- condition is the pair of theirs.                                    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.Product using (_×_; _,_)

open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; lo; hi; uᵇ; _·ᵇ_; two-sided; _≾ᵇ_)

open import DenotationalSemantics.Model.World

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.LeftSided
  as Lo
import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.RightSided
  as Hi

open Lo Op _≟ₒ_ cost using () renaming
  (_⊑ᵗ[_]_ to _⊑ˡᵒ[_]_; ⊑ᵗ-refl to ⊑ˡᵒ-refl; ⊑ᵗ-trans to ⊑ˡᵒ-trans;
   ⊑ᵗ-mono to ⊑ˡᵒ-mono; ⊑ᵗ-irrelevant to ⊑ˡᵒ-irrelevant)
open Hi Op _≟ₒ_ cost using () renaming
  (_⊑ᵗ[_]_ to _⊑ʰⁱ[_]_; ⊑ᵗ-refl to ⊑ʰⁱ-refl; ⊑ᵗ-trans to ⊑ʰⁱ-trans;
   ⊑ᵗ-mono to ⊑ʰⁱ-mono; ⊑ᵗ-irrelevant to ⊑ʰⁱ-irrelevant)

------------------------------------------------------------------------
-- The frame

_⊑ᵗ[_]_ : ℕ → TwoSided → ℕ → Set
w ⊑ᵗ[ i ] w' = (w ⊑ˡᵒ[ lo i ] w') × (w ⊑ʰⁱ[ hi i ] w')

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ uᵇ ] w
⊑ᵗ-refl {w} = ⊑ˡᵒ-refl {w} , ⊑ʰⁱ-refl {w}

⊑ᵗ-trans : ∀ {i₁ i₂ w w' w''}
         → w ⊑ᵗ[ i₁ ] w' → w' ⊑ᵗ[ i₂ ] w'' → w ⊑ᵗ[ i₁ ·ᵇ i₂ ] w''
⊑ᵗ-trans {i₁} {i₂} (l₁ , h₁) (l₂ , h₂) =
    ⊑ˡᵒ-trans {lo i₁} {lo i₂} l₁ l₂ , ⊑ʰⁱ-trans {hi i₁} {hi i₂} h₁ h₂

⊑ᵗ-mono : ∀ {i₁ i₂ w w'} → i₁ ≾ᵇ i₂ → w ⊑ᵗ[ i₁ ] w' → w ⊑ᵗ[ i₂ ] w'
⊑ᵗ-mono {i₁} {i₂} (l , h) (pl , ph) =
    ⊑ˡᵒ-mono {lo i₁} {lo i₂} l pl , ⊑ʰⁱ-mono {hi i₁} {hi i₂} h ph

⊑ᵗ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵗ[ i ] w') → p ≡ q
⊑ᵗ-irrelevant {i} (l , h) (l' , h') =
  cong₂ _,_ (⊑ˡᵒ-irrelevant {lo i} l l') (⊑ʰⁱ-irrelevant {hi i} h h')

ticks : World two-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {i₁} {i₂} → ⊑ᵗ-trans {i₁} {i₂}
  ; ⊑-mono       = λ {i₁} {i₂} → ⊑ᵗ-mono {i₁} {i₂}
  ; ⊑-irrelevant = λ {i} → ⊑ᵗ-irrelevant {i}
  }
