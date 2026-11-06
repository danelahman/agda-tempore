------------------------------------------------------------------------
-- The context modality on renamings, at particular grades            --
--                                                                    --
-- `Renaming/ContextModality` shows when the context modality         --
-- `L_ρ = _⟨ ρ ⟩` has a left adjoint, and when it is a PRA.           --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.ContextModality where

-- upper bounds: an obstruction to being a parametric right adjoint,
-- and the eternal context where it disappears

import MonomorphicCalculus.Examples.ContextModality.UpperBound

-- both bounds: the obstruction at a grade not above the unit

import MonomorphicCalculus.Examples.ContextModality.Interval

-- lower bounds: a parametric right adjoint at every grade

import MonomorphicCalculus.Examples.ContextModality.LowerBound

-- whether the unit is the greatest grade, grade by grade

import MonomorphicCalculus.Examples.ContextModality.Survey
