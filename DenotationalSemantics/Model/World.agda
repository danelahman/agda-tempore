------------------------------------------------------------------------
-- The Kripke frame of worlds that the presheaf semantics is indexed   --
-- by.                                                                  --
--                                                                    --
-- The frame carries *no* monoid structure on its carrier of worlds.   --
-- A presheaf is discretely indexed by the worlds `W` (see              --
-- `DenotationalSemantics.Model.Example.PSh.Base`); the order only      --
-- enters through the modalities. Accordingly, the only structure the   --
-- frame provides is a family of preorders on worlds,                  --
--                                                                    --
--     _⊑[ ρ ]_  :  W → W → Set ,                                       --
--                                                                    --
-- *graded* by the resource grades `ρ : R`, together with the natural  --
-- laws that make the box modality (Kripke necessity) and the context  --
-- modality (Kripke possibility) into a graded comonad / monad:        --
--                                                                    --
--   * `⊑-refl`  : reflexivity at the unit grade `uᵣ`;                  --
--   * `⊑-trans` : composition, which *multiplies* the grades;         --
--   * `⊑-mono`  : the relation shrinks as the grade grows (a larger    --
--                 resource budget is a weaker demand);                 --
--   * `⊑-irrelevant` : the accessibility witnesses are proof           --
--                 irrelevant, which is what makes every graded         --
--                 (co)monad coherence law hold on the nose.            --
--                                                                    --
-- With `_⊑[ ρ ]_` possibly empty for some worlds/grades, resources    --
-- can *expire*: e.g. with two-sided time-interval grades a world may   --
-- have no `ρ`-successor once the interval has passed.                  --
--                                                                    --
-- Later this will be extended with a second family of orders graded    --
-- by effect grades, for the semantics of the effectful modality.       --
------------------------------------------------------------------------

open import Syntax.Grades

open import Util.Equality

module DenotationalSemantics.Model.World (Rg : Grade) where

open Grade Rg
  renaming (Carrier to R; _·_ to _·ᵣ_; u to uᵣ; _≾_ to _≾ᵣ_)

record World : Set₁ where

  infix 5 _⊑[_]_

  field

    -- STRUCTURE

    -- carrier of worlds
    W : Set₀

    -- the resource-grade-indexed accessibility relation
    _⊑[_]_ : W → R → W → Set₀

    -- PROPERTIES

    -- reflexivity holds at the unit grade
    ⊑-refl : ∀ {w} → w ⊑[ uᵣ ] w

    -- transitivity multiplies the grades
    ⊑-trans : ∀ {ρ₁ ρ₂ w w' w''}
            → w ⊑[ ρ₁ ] w' → w' ⊑[ ρ₂ ] w'' → w ⊑[ ρ₁ ·ᵣ ρ₂ ] w''

    -- a larger grade gives a smaller relation
    ⊑-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵣ ρ₂ → w ⊑[ ρ₂ ] w' → w ⊑[ ρ₁ ] w'

    -- accessibility witnesses are proof irrelevant
    ⊑-irrelevant : ∀ {ρ w w'} → (p q : w ⊑[ ρ ] w') → p ≡ q
