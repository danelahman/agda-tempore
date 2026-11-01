--------------------------------------------------------------------------
-- The lock `L_ρ = _⟨ ρ ⟩` on renamings, at particular grades.          --
--                                                                      --
-- `Renaming/Lock` shows that `L_ρ` has a left adjoint only at the unit --
-- and is a parametric right adjoint at every grade exactly when the    --
-- unit is the greatest grade. The examples instantiate both sides.     --
--------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Lock where

-- upper bounds: an obstruction to being a parametric right adjoint,
-- and the eternal context where it disappears

import MonomorphicCalculus.Examples.Lock.RightSided

-- both bounds: the obstruction at a grade not above the unit

import MonomorphicCalculus.Examples.Lock.TwoSided

-- lower bounds: a parametric right adjoint at every grade

import MonomorphicCalculus.Examples.Lock.LeftSided

-- whether the unit is the greatest grade, grade by grade

import MonomorphicCalculus.Examples.Lock.Survey
