------------------------------------------------------------------------
-- A time-ticks Kripke frame for the two-sided subset intervals.       --
--                                                                    --
-- Worlds are time points `ℕ`, and a grade `[ P , Q ]` fences the      --
-- advance in from both sides:                                        --
--                                                                    --
--   w ⊑ᵗ[ [ P , Q ] ] w'  iff  w + durationˡᵒ p ≤ w'  for *all* p ∈ P --
--                         and  w' ≤ w + durationʰⁱ q  for *some* q ∈ Q --
--                                                                    --
-- The two quantifiers differ because the two endpoints weaken in      --
-- opposite directions of inclusion: below, weakening drops members,   --
-- so the condition must be asked of all of them; above, weakening     --
-- adds members, so one is enough.                                    --
--                                                                    --
-- Each half is the corresponding one-sided frame, at its own cost     --
-- model, and every frame condition is the pair of theirs.             --
--                                                                    --
-- The top `unconstrained` stands above the pairs, and fences the      --
-- advance in from neither side, so it relates every pair of worlds.  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costˡᵒ costʰⁱ : Op → ℕ) where

open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; lo; hi; two-sided; Interval; between_; unconstrained;
         uᴵ; _·ᴵ_; _≾ᴵ_)

-- each endpoint of a pair is an un-extended set, which the one-sided
-- frames see through their own injections

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (demanding_)
open import Syntax.Grades.Example.Traces.Subsets.RightSided Op _≟ₒ_
  using (permitting_)

open import DenotationalSemantics.Model.World

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.LeftSided
  as Lo
import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.RightSided
  as Hi

open Lo Op _≟ₒ_ costˡᵒ using () renaming
  (_⊑ᵗ[_]_ to _⊑ˡᵒ[_]_; ⊑ᵗ-refl to ⊑ˡᵒ-refl; ⊑ᵗ-trans to ⊑ˡᵒ-trans;
   ⊑ᵗ-mono to ⊑ˡᵒ-mono; ⊑ᵗ-irrelevant to ⊑ˡᵒ-irrelevant)
open Hi Op _≟ₒ_ costʰⁱ using () renaming
  (_⊑ᵗ[_]_ to _⊑ʰⁱ[_]_; ⊑ᵗ-refl to ⊑ʰⁱ-refl; ⊑ᵗ-trans to ⊑ʰⁱ-trans;
   ⊑ᵗ-mono to ⊑ʰⁱ-mono; ⊑ᵗ-irrelevant to ⊑ʰⁱ-irrelevant)

------------------------------------------------------------------------
-- The frame

_⊑ᵗ[_]_ : ℕ → Interval → ℕ → Set
w ⊑ᵗ[ (between i) ] w' =
    (w ⊑ˡᵒ[ (demanding (lo i)) ] w')
  × (w ⊑ʰⁱ[ (permitting (hi i)) ] w')
w ⊑ᵗ[ unconstrained ]      w' = ⊤

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ uᴵ ] w
⊑ᵗ-refl {w} = ⊑ˡᵒ-refl {w} , ⊑ʰⁱ-refl {w}

⊑ᵗ-trans : ∀ {i₁ i₂ w w' w''}
         → w ⊑ᵗ[ i₁ ] w' → w' ⊑ᵗ[ i₂ ] w'' → w ⊑ᵗ[ i₁ ·ᴵ i₂ ] w''
⊑ᵗ-trans {between _}  {unconstrained}      p q = tt
⊑ᵗ-trans {unconstrained}     {_}        p q = tt
⊑ᵗ-trans {between i₁} {between i₂} (l₁ , h₁) (l₂ , h₂) =
    ⊑ˡᵒ-trans {demanding (lo i₁)} {demanding (lo i₂)} l₁ l₂
  , ⊑ʰⁱ-trans {permitting (hi i₁)} {permitting (hi i₂)} h₁ h₂

⊑ᵗ-mono : ∀ {i₁ i₂ w w'} → i₁ ≾ᴵ i₂ → w ⊑ᵗ[ i₁ ] w' → w ⊑ᵗ[ i₂ ] w'
⊑ᵗ-mono {_}       {unconstrained}      rel p = tt
⊑ᵗ-mono {unconstrained}     {between _}  ()
⊑ᵗ-mono {between i₁} {between i₂} (l , h) (pl , ph) =
    ⊑ˡᵒ-mono {demanding (lo i₁)} {demanding (lo i₂)} l pl
  , ⊑ʰⁱ-mono {permitting (hi i₁)} {permitting (hi i₂)} h ph

⊑ᵗ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵗ[ i ] w') → p ≡ q
⊑ᵗ-irrelevant {between i} (l , h) (l' , h') =
  cong₂ _,_ (⊑ˡᵒ-irrelevant {demanding (lo i)} l l')
            (⊑ʰⁱ-irrelevant {permitting (hi i)} h h')
⊑ᵗ-irrelevant {unconstrained}    tt      tt        = refl

ticks : World two-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {i₁} {i₂} → ⊑ᵗ-trans {i₁} {i₂}
  ; ⊑-mono       = λ {i₁} {i₂} → ⊑ᵗ-mono {i₁} {i₂}
  ; ⊑-irrelevant = λ {i} → ⊑ᵗ-irrelevant {i}
  }
