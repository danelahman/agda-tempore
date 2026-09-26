------------------------------------------------------------------
-- Invariants of the solver                                       --
------------------------------------------------------------------

open import Syntax.LanguageSpec

module TypeInference.SolverImpl.Invariants (S : LanguageSpec) where

-- Unknowns free in the images of a substitution; good sides, types
-- and substitutions

open import TypeInference.SolverImpl.Invariants.Outer S public

-- I1′ and I5 on a residual, and the invariant of a state

open import TypeInference.SolverImpl.Invariants.Residual S public

-- Membership in a sum; skeletons kept by grouping and pruning

open import TypeInference.SolverImpl.Invariants.Alts S public

-- Canonical forms: a whole unknown kept whole, no unknown added

open import TypeInference.SolverImpl.Invariants.Canon S public
