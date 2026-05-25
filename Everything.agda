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

open import Syntax.LanguageSpec

module Everything (S : LanguageSpec) where

-- UTILS
--------

---- Equality

open import Util.Equality


-- SYNTAX
---------

---- Syntax of the language

open import Syntax.Types    S
open import Syntax.Contexts S
open import Syntax.Language S

---- Renamings and substitutions

open import Syntax.Renamings     S
open import Syntax.RenActions    S
open import Syntax.Substitutions S

---- Computation term and evaluation contexts

open import Syntax.CompContext S


-- GRADES
---------

---- Grades and grade morphisms

open import Syntax.Grades

---- Examples of grades

open import Syntax.Grades.LeftSidedIntervals
open import Syntax.Grades.RightSidedIntervals
open import Syntax.Grades.TwoSidedIntervals
open import Syntax.Grades.IntGradeSystem


-- OPERATIONAL SEMANTICS
------------------------

---- States of operational semantics

open import OperationalSemantics.State S

---- Small-step operational semantics and preservation theorem

open import OperationalSemantics.PreservationTheorem S

---- Progress theorem

open import OperationalSemantics.ProgressTheorem S

---- Top-level operational semantics

open import OperationalSemantics.TopLevelOpSemantics S

---- Top-level preservation theorem

open import OperationalSemantics.TopLevelPreservationTheorem S

---- Top-level progress theorem

open import OperationalSemantics.TopLevelProgressTheorem S


-- EQUATIONAL THEORY
--------------------

open import EquationalTheory.EquationalTheory S

---- Equational soundness theorem (Thm 4.9 of Ahman & Žajdela)

open import EquationalTheory.EquationalSoundness S
