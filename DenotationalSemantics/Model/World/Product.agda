------------------------------------------------------------------------
-- The product of two Kripke frames.                                  --
--                                                                    --
-- A frame for `G₁` and one for `G₂` give a frame for `G₁ ×ᵍ G₂`: a   --
-- world is a pair of worlds, and accessibility at `(ρ₁ , ρ₂)` holds  --
-- componentwise:                                                     --
--                                                                    --
--   (w₁ , w₂) ⊑[ (ρ₁ , ρ₂) ] (w₁' , w₂')                             --
--     iff   w₁ ⊑[ ρ₁ ] w₁'   and   w₂ ⊑[ ρ₂ ] w₂'                    --
--                                                                    --
-- Every law holds componentwise, with no condition on either frame.  --
------------------------------------------------------------------------

module DenotationalSemantics.Model.World.Product where

open import Data.Product using (_×_; _,_)

open import Syntax.Durations using (Duration)
open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)

open import Util.Equality

open import DenotationalSemantics.Model.World

infixr 2 _⊗_

_⊗_ : {D : Duration} {G₁ G₂ : Grade D} → World G₁ → World G₂ → World (G₁ ×ᵍ G₂)
F₁ ⊗ F₂ = record
  { W            = F₁.W × F₂.W
  ; _⊑[_]_       = λ (w₁ , w₂) (ρ₁ , ρ₂) (w₁' , w₂') →
                     (w₁ F₁.⊑[ ρ₁ ] w₁') × (w₂ F₂.⊑[ ρ₂ ] w₂')
  ; ⊑-refl       = F₁.⊑-refl , F₂.⊑-refl
  ; ⊑-trans      = λ (p₁ , p₂) (q₁ , q₂) → F₁.⊑-trans p₁ q₁ , F₂.⊑-trans p₂ q₂
  ; ⊑-mono       = λ (r₁ , r₂) (p₁ , p₂) → F₁.⊑-mono r₁ p₁ , F₂.⊑-mono r₂ p₂
  ; ⊑-irrelevant = λ (p₁ , p₂) (q₁ , q₂) →
                     cong₂ _,_ (F₁.⊑-irrelevant p₁ q₁) (F₂.⊑-irrelevant p₂ q₂)
  }
  where
    module F₁ = World F₁
    module F₂ = World F₂
