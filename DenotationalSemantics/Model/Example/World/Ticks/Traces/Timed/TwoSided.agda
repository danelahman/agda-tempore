------------------------------------------------------------------------
-- A time-ticks Kripke frame for the two-sided trace intervals.        --
--                                                                    --
-- Worlds are time points `ℕ`, and a grade `[ P , Q ]` fences the      --
-- advance in from both sides at once:                                --
--                                                                    --
--   w ⊑ᵗ[ [ P , Q ] ] w'   iff   w + duration p ≤ w'  for some p ∈ P --
--                          and   w' ≤ w + duration q  for some q ∈ Q --
--                                                                    --
-- Each half is the corresponding one-sided frame -- the floor's from  --
-- `Ticks.Traces.Timed.LeftSided`, the cap's from                   --
-- `Ticks.Traces.Timed.RightSided` -- and every frame condition is --
-- the pair of theirs, the grade's monoid and order both acting        --
-- endpointwise.                                                      --
--                                                                    --
-- The two witnesses are independent: the guarantee that fixes how far --
-- the advance must reach need not be the allowance that caps it. What --
-- the coherence field of the grade buys is that the fence is not      --
-- empty -- some listed guarantee takes no longer than some listed     --
-- allowance -- so a world at the far end is reachable at all.         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Syntax.Grades.Example.Traces.Timed.TwoSided Op _≟ₒ_ cost cost-pos
  using (TwoSided; lo; hi; uᵗˢ; _·ᵗˢ_; two-sided; _≾ᵗˢ_)

open import DenotationalSemantics.Model.World

-- the two halves, each at its own order

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.LeftSided
  as Lo
import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.RightSided
  as Hi

open Lo Op _≟ₒ_ cost using () renaming
  (_⊑ᵗ[_]_ to _⊑ˡᵒ[_]_; ⊑ᵗ-refl to ⊑ˡᵒ-refl; ⊑ᵗ-trans to ⊑ˡᵒ-trans;
   ⊑ᵗ-mono to ⊑ˡᵒ-mono; ⊑ᵗ-irrelevant to ⊑ˡᵒ-irrelevant)
open Hi Op _≟ₒ_ cost cost-pos using () renaming
  (_⊑ᵗ[_]_ to _⊑ʰⁱ[_]_; ⊑ᵗ-refl to ⊑ʰⁱ-refl; ⊑ᵗ-trans to ⊑ʰⁱ-trans;
   ⊑ᵗ-mono to ⊑ʰⁱ-mono; ⊑ᵗ-irrelevant to ⊑ʰⁱ-irrelevant)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: far enough for one of the guarantees,
-- and no further than one of the allowances.

_⊑ᵗ[_]_ : ℕ → TwoSided → ℕ → Set
w ⊑ᵗ[ i ] w' = (w ⊑ˡᵒ[ lo i ] w') × (w ⊑ʰⁱ[ hi i ] w')

-- reflexivity at the unit grade: neither endpoint asks for time to pass

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ uᵗˢ ] w
⊑ᵗ-refl {w} = ⊑ˡᵒ-refl {w} , ⊑ʰⁱ-refl {w}

-- transitivity multiplies the grades, endpointwise

⊑ᵗ-trans : ∀ {i₁ i₂ w w' w''}
         → w ⊑ᵗ[ i₁ ] w' → w' ⊑ᵗ[ i₂ ] w''
         → w ⊑ᵗ[ i₁ ·ᵗˢ i₂ ] w''
⊑ᵗ-trans {i₁} {i₂} (l₁ , h₁) (l₂ , h₂) =
    ⊑ˡᵒ-trans {lo i₁} {lo i₂} l₁ l₂
  , ⊑ʰⁱ-trans {hi i₁} {hi i₂} h₁ h₂

-- covariance: a weaker guarantee reaches no further, a larger allowance
-- caps no tighter

⊑ᵗ-mono : ∀ {i₁ i₂ w w'} → i₁ ≾ᵗˢ i₂ → w ⊑ᵗ[ i₁ ] w' → w ⊑ᵗ[ i₂ ] w'
⊑ᵗ-mono {i₁} {i₂} (l , h) (pl , ph) =
    ⊑ˡᵒ-mono {lo i₁} {lo i₂} l pl
  , ⊑ʰⁱ-mono {hi i₁} {hi i₂} h ph

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
