--------------------------------------------------------------------------
-- Agda formalisation of the syntax and semantics of a core language    --
-- for programming with temporal resources using modal types.           --
--                                                                      --
-- The language has:                                                    --
--                                                                      --
--   - a modality on types that specifies that data might not yet be    --
--     available, but is guaranteed to be in at most τ time steps       --
--                                                                      --
--   - a modality on contexts describing that at least τ time steps     --
--     have passed (allowing new data to become available)              --
--                                                                      --
--   - features facilitating the interaction of these two modalities    --
--     based on adjunctions (i.e., Fitch-style modal type systems)      --
--                                                                      --
--   - computational effects modelled using algebraic operations with   --
--     prescribed execution times and whose execution makes time pass   --
--     (both in the semantics and also in the static typing rules)      --
--                                                                      --
-- The formalisation includes:                                          --
--                                                                      --
--   - syntax and type system of the language                           --
--                                                                      --
--   - actions of renamings and substitutions                           --
--                                                                      --
--   - small-step stateful time-aware operational semantics             --
--                                                                      --
--   - progress and preservation theorems                               --
--                                                                      --
--   - equational theory based on standard presentations of local state --
--------------------------------------------------------------------------

open import Syntax.Grades

module Everything (Grades : GradeSystem) where

open GradeSystemInterface Grades

-- UTILS
--------

---- Equality

open import Util.Equality

---- Algebraic operations

open import Util.Operations (Grades)


-- SYNTAX
---------

---- Syntax of the language

open import Syntax.Types (Grades)
open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)

---- Renamings and substitutions

open import Syntax.Renamings (Grades)
open import Syntax.Substitutions (Grades)

---- Computation term and evaluation contexts

open import Syntax.CompContext (Grades)

-- GRADES
---------

open import Syntax.Grades.OneSidedIntervals (Grades)
open import Syntax.Grades.TwoSidedIntervals (Grades)

-- OPERATIONAL SEMANTICS
------------------------

---- States of operational semantics

open import OperationalSemantics.State (Grades)

---- Small-step operational semantics and preservation theorem 

open import OperationalSemantics.PreservationTheorem (Grades)

---- Progress theorem

open import OperationalSemantics.ProgressTheorem (Grades)


-- EQUATIONAL THEORY
--------------------

open import EquationalTheory.EquationalTheory (Grades)

---- Equational soundness theorem (Thm 4.9 of Ahman & Žajdela)

open import EquationalTheory.EquationalSoundness (Grades)
