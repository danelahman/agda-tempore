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

module Everything where

-- UTILS
--------

---- Equality

open import Util.Equality


-- SYNTAX
---------

---- Syntax of the language

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

---- Renamings and substitutions

open import Syntax.Renamings
open import Syntax.RenActions
open import Syntax.Substitutions

---- Computation term and evaluation contexts

open import Syntax.CompContext


-- GRADES
---------

---- Grades and grade morphisms

open import Syntax.Grades

---- Examples of time-based grades

open import Syntax.Grades.Time.LeftSidedIntervals
open import Syntax.Grades.Time.RightSidedIntervals
open import Syntax.Grades.Time.TwoSidedIntervals

---- Utilities for trace-based grades

open import Syntax.Grades.Traces.Restriction
open import Syntax.Grades.Traces.Durations
open import Syntax.Grades.Traces.MaxDuration
open import Syntax.Grades.Traces.MinDuration

---- Examples of trace-based grades

open import Syntax.Grades.Traces.RightSidedTraces
open import Syntax.Grades.Traces.LeftSidedTraces
open import Syntax.Grades.Traces.TwoSidedTraces

---- Examples of grade systems

open import Syntax.Grades.GradeSystem.TwoSidedTimeIntervalsToOneSidedTimeIntervals

open import Syntax.Grades.GradeSystem.TwoSidedTraceIntervalsToLeftSidedTraceIntervals

open import Syntax.Grades.GradeSystem.TwoSidedTraceIntervalsToTwoSidedTimeIntervals
open import Syntax.Grades.GradeSystem.TwoSidedTraceIntervalsToTwoSidedTimeIntervalsWorstCase

-- OPERATIONAL SEMANTICS
------------------------

---- States of operational semantics

open import OperationalSemantics.State

---- Small-step operational semantics and preservation theorem

open import OperationalSemantics.PreservationTheorem

---- Progress theorem

open import OperationalSemantics.ProgressTheorem

---- Top-level operational semantics

open import OperationalSemantics.TopLevelOpSemantics

---- Top-level preservation theorem

open import OperationalSemantics.TopLevelPreservationTheorem

---- Top-level progress theorem

open import OperationalSemantics.TopLevelProgressTheorem


-- EQUATIONAL THEORY
--------------------

open import EquationalTheory.EquationalTheory

---- Equational soundness theorem (Thm 4.9 of Ahman & Žajdela)

open import EquationalTheory.EquationalSoundness
