------------------------------------------------------------------------
-- The Kripke frame of worlds that the presheaf semantics is indexed   --
-- by.                                                                  --
--                                                                    --
-- The frame carries *no* monoid structure on its carrier of worlds.   --
-- A presheaf is discretely indexed by the worlds `W` (see              --
-- `DenotationalSemantics.Model.Example.PSh.Base`); the orders only     --
-- enter through the modalities and the monad. Accordingly, the only    --
-- structure the frame provides is two families of preorders on         --
-- worlds:                                                              --
--                                                                    --
--   * `_⊑[ ρ ]_`  , graded by the *resource* grades `ρ : R`, driving   --
--     the box and context modalities (Kripke necessity / possibility); --
--                                                                    --
--   * `_⊑ᵉ[ ε ]_` , graded by the *effect* grades `ε : E`, driving     --
--     the operations and delays of the graded effect monad.            --
--                                                                    --
-- Each family has the natural laws that make the (co)monad / monad     --
-- coherences hold on the nose (reflexivity at the unit grade,          --
-- transitivity multiplying the grades, *covariance* in the grade —     --
-- a larger grade gives a larger relation — and proof irrelevance of    --
-- the witnesses). Covariance is what makes the box modality             --
-- contravariantly graded (`∀`-shaped) and the context modality and     --
-- effect monad covariantly graded (`Σ`-shaped). Finally, `⊑ᵉ-resource` --
-- links the two: every effect-accessibility fact projects to a         --
-- resource-accessibility fact along the effect-to-resource morphism    --
-- `mapᵉ`. This is what lets the monad's strength thread a box          --
-- `[ mapᵉ ε ] A` (which quantifies over `_⊑[ mapᵉ ε ]_`) along the     --
-- worlds a computation of grade `ε` reaches (via `_⊑ᵉ[ ε ]_`).         --
------------------------------------------------------------------------

open import Syntax.Grades

open import Util.Equality

module DenotationalSemantics.Model.World (GS : GradeSystem) where

open GradeSystemInterface GS

record World : Set₁ where

  infix 5 _⊑[_]_
  infix 5 _⊑ᵉ[_]_

  field

    -- STRUCTURE

    -- carrier of worlds (a bare set — no operations)
    W : Set₀

    -- the resource-grade-indexed accessibility relation
    _⊑[_]_ : W → R → W → Set₀

    -- the effect-grade-indexed accessibility relation
    _⊑ᵉ[_]_ : W → E → W → Set₀

    -- PROPERTIES

    -- resource accessibility is a graded preorder

    ⊑-refl : ∀ {w} → w ⊑[ uᵣ ] w
    ⊑-trans : ∀ {ρ₁ ρ₂ w w' w''}
            → w ⊑[ ρ₁ ] w' → w' ⊑[ ρ₂ ] w'' → w ⊑[ ρ₁ ·ᵣ ρ₂ ] w''
    ⊑-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵣ ρ₂ → w ⊑[ ρ₁ ] w' → w ⊑[ ρ₂ ] w'
    ⊑-irrelevant : ∀ {ρ w w'} → (p q : w ⊑[ ρ ] w') → p ≡ q

    -- effect accessibility is a graded preorder

    ⊑ᵉ-refl : ∀ {w} → w ⊑ᵉ[ uₑ ] w
    ⊑ᵉ-trans : ∀ {ε₁ ε₂ w w' w''}
             → w ⊑ᵉ[ ε₁ ] w' → w' ⊑ᵉ[ ε₂ ] w'' → w ⊑ᵉ[ ε₁ ·ₑ ε₂ ] w''
    ⊑ᵉ-mono : ∀ {ε₁ ε₂ w w'} → ε₁ ≾ₑ ε₂ → w ⊑ᵉ[ ε₁ ] w' → w ⊑ᵉ[ ε₂ ] w'
    ⊑ᵉ-irrelevant : ∀ {ε w w'} → (p q : w ⊑ᵉ[ ε ] w') → p ≡ q

    -- effect accessibility projects to resource accessibility along `mapᵉ`

    ⊑ᵉ-resource : ∀ {ε w w'} → w ⊑ᵉ[ ε ] w' → w ⊑[ mapᵉ ε ] w'

    -- the effect grade order is proof irrelevant. The effect monad's
    -- sub-effecting (the semantics of `coerce`) carries a `≾ₑ`-witness
    -- in its tree; this makes `coerce` a proof-irrelevant congruence
    -- (the only law the equational theory imposes on it), and keeps the
    -- monad laws holding in the presence of sub-effecting nodes. All the
    -- concrete effect-grade instances (intervals, …) satisfy it.

    ≾ₑ-irrelevant : ∀ {ε₁ ε₂} → (p q : ε₁ ≾ₑ ε₂) → p ≡ q
