------------------------------------------------------------------------
-- The context modality on renamings, at particular grades            --
--                                                                    --
-- `Typing/Renaming/ContextModality` shows that `L_ρ = _⟨ ρ ⟩` has a  --
-- left adjoint, equivalently is a parametric right adjoint, iff      --
-- every context has a lowering by `ρ`, and that a left adjoint       --
-- needs the residuals by `ρ` of the grades below `⊤ · ρ`.            --
------------------------------------------------------------------------

module PolymorphicCalculus.Examples.ContextModality where

-- upper bounds: residuals by truncated subtraction, a left adjoint at
-- every grade

import PolymorphicCalculus.Examples.ContextModality.UpperBound

-- lower bounds: residuals of the grades below `⊤ · ρ`, a left adjoint at
-- every grade

import PolymorphicCalculus.Examples.ContextModality.LowerBound

-- intervals: a grade below `⊤ · [1,2]` without a residual, no left
-- adjoint at `[1,2]`

import PolymorphicCalculus.Examples.ContextModality.Interval
