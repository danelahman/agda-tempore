--------------------------------------------------------------------------
-- The Kripke frame of worlds that the presheaf semantics is indexed    --
-- by.                                                                  --
--                                                                      --
-- The frame carries no monoid structure on its carrier of worlds. In   --
-- `MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base`   --
-- a presheaf is indexed by the worlds `W` monotonely in the unit grade --
-- only; the graded order enters through the modalities and the monad.  --
-- The frame provides a single family of preorders on worlds,           --
-- `_⊑[ ρ ]_`, graded by the resource grades `ρ : R`, driving the box   --
-- and context modalities (Kripke necessity / possibility) and the      --
-- world-movement of the graded effect monad.                           --
--                                                                      --
-- The monad is graded by the effect grades `ε : E`, but it moves       --
-- through the worlds along the resource projection `mapᵉ ε` of its     --
-- effect: an operation of grade `op-grade op` advances the worlds by   --
-- `mapᵉ (op-grade op)` resources, matching the box `[ mapᵉ (op-grade   --
-- op) ]` that the calculus's operations and handlers use. No separate  --
-- effect-graded accessibility is needed: the worlds may carry as much  --
-- history as desired, and `_⊑[_]_` relates those worlds.               --
--                                                                      --
-- The family has the natural laws that make the (co)monad / monad      --
-- coherences hold on the nose (reflexivity at the unit grade,          --
-- transitivity multiplying the grades, covariance in the grade, so     --
-- that a larger grade gives a larger relation, and proof irrelevance   --
-- of the witnesses). Covariance is what makes the box modality         --
-- contravariantly graded (`∀`-shaped) and the context modality and     --
-- effect monad covariantly graded (`Σ`-shaped).                        --
--------------------------------------------------------------------------

open import Grades.Durations using (Duration)
open import Grades.Base

open import Util.Equality

module MonomorphicCalculus.DenotationalSemantics.Model.World {D : Duration} (RG : Grade D) where

open Grade RG using () renaming
  (Carrier to R;
   u to uᵣ;
   _·_ to _·ᵣ_;
   _≾_ to _≾ᵣ_)

record World : Set₁ where

  infix 5 _⊑[_]_

  field

    -- STRUCTURE

    -- carrier of worlds (a bare set, no operations)
    W : Set₀

    -- the resource-grade-indexed accessibility relation
    _⊑[_]_ : W → R → W → Set₀

    -- PROPERTIES

    -- resource accessibility is a graded preorder

    ⊑-refl : ∀ {w} → w ⊑[ uᵣ ] w
    ⊑-trans : ∀ {ρ₁ ρ₂ w w' w''}
            → w ⊑[ ρ₁ ] w' → w' ⊑[ ρ₂ ] w'' → w ⊑[ ρ₁ ·ᵣ ρ₂ ] w''
    ⊑-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵣ ρ₂ → w ⊑[ ρ₁ ] w' → w ⊑[ ρ₂ ] w'
    ⊑-irrelevant : ∀ {ρ w w'} → (p q : w ⊑[ ρ ] w') → p ≡ q
