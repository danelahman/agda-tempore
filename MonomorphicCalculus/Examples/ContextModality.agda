------------------------------------------------------------------------
-- The context modality on renamings, at particular grades            --
--                                                                    --
-- `Renaming/ContextModality` shows that the context modality         --
-- `L_ρ = _⟨ ρ ⟩` has a left adjoint only at the unit, and that it is --
-- a parametric right adjoint at every grade exactly when the unit is --
-- the greatest grade. The examples instantiate both sides.           --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.ContextModality where

-- upper bounds: an obstruction to being a parametric right adjoint,
-- and the eternal context where it disappears

import MonomorphicCalculus.Examples.ContextModality.RightSided

-- both bounds: the obstruction at a grade not above the unit

import MonomorphicCalculus.Examples.ContextModality.TwoSided

-- lower bounds: a parametric right adjoint at every grade

import MonomorphicCalculus.Examples.ContextModality.LeftSided

-- whether the unit is the greatest grade, grade by grade

import MonomorphicCalculus.Examples.ContextModality.Survey
