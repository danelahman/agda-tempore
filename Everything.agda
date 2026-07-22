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
--                                                                      --
--   - a denotational semantics: an abstract model interface (worlds,   --
--     box and context modalities, their adjunction, and a graded       --
--     effect monad), a concrete model on presheaves over the worlds,   --
--     and the interpretation of the language in any such model         --
--                                                                      --
--   - soundness of the operational semantics with respect to the       --
--     denotational semantics                                           --
--------------------------------------------------------------------------

open import Syntax.LanguageSpec

module Everything where

-- UTILS
--------

---- Equality

open import Util.Equality

---- Monad helper

open import Util.Monad


-- SYNTAX
---------

---- Base types, operations, and ground types
---- (the language specification `Syntax.LanguageSpec` is imported above)

open import Syntax.BaseTypes
open import Syntax.Operations
open import Syntax.GroundTypes

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

open import Syntax.Grades.LeftSidedTimeIntervals
open import Syntax.Grades.RightSidedTimeIntervals
open import Syntax.Grades.TwoSidedTimeIntervals
open import Syntax.Grades.TwoSidedTimeIntervalsWithInfinity

---- Utilities for trace-based grades

open import Syntax.Grades.Traces.Base
open import Syntax.Grades.Traces.Restriction
open import Syntax.Grades.Traces.Durations
open import Syntax.Grades.Traces.MaxDuration
open import Syntax.Grades.Traces.MinDuration
open import Syntax.Grades.Traces.Subtrace

---- Examples of trace-based grades

open import Syntax.Grades.SetOfTraces
open import Syntax.Grades.SetOfTracesUpToSubtrace

---- Examples of grade systems

open import Syntax.Grades.GradeSystem.TwoSidedIntervalsToLeftSidedIntervals

open import Syntax.Grades.GradeSystem.TracesToRestrictedTraces

open import Syntax.Grades.GradeSystem.TracesToTimeIntervals

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

-- open import EquationalTheory.EquationalSoundness


-- DENOTATIONAL SEMANTICS
-------------------------

---- Abstract model interface

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.Modality.Eternal
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad
open import DenotationalSemantics.Model.Monad.Enrichment
open import DenotationalSemantics.Model.TickMonad
open import DenotationalSemantics.Model.Implementation

---- Concrete model on setoid-valued presheaves over the worlds

open import DenotationalSemantics.Model.Example.PSh.Base
open import DenotationalSemantics.Model.Example.PSh.Modality.Future
open import DenotationalSemantics.Model.Example.PSh.Modality.Past
open import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction
open import DenotationalSemantics.Model.Example.PSh.Modality.Eternal
open import DenotationalSemantics.Model.Example.PSh.Monad.Core
open import DenotationalSemantics.Model.Example.PSh.Monad.Effects
open import DenotationalSemantics.Model.Example.PSh.Monad.Handling
open import DenotationalSemantics.Model.Example.PSh.Monad.Instance
open import DenotationalSemantics.Model.Example.PSh.TickMonad
open import DenotationalSemantics.Model.Example.PSh.Implementation
open import DenotationalSemantics.Model.Example.PSh.TopLevelInstance

---- Interpretation of the calculus

open import DenotationalSemantics.Interpretation.Types
open import DenotationalSemantics.Interpretation.Contexts
open import DenotationalSemantics.Interpretation.Variables
open import DenotationalSemantics.Interpretation.Terms
open import DenotationalSemantics.Interpretation.Renaming
open import DenotationalSemantics.Interpretation.RenamingCoherence
open import DenotationalSemantics.Interpretation.SubstitutionCoherence
open import DenotationalSemantics.Interpretation.State

---- Soundness of the equational theory with respect to the interpretation

open import EquationalTheory.Soundness.Base
open import EquationalTheory.Soundness.Parametric
open import EquationalTheory.Soundness.Values
open import EquationalTheory.Soundness.Modal
open import EquationalTheory.Soundness.Coerce
open import EquationalTheory.Soundness.Seq
open import EquationalTheory.Soundness.SeqAssoc
open import EquationalTheory.Soundness.Delay
open import EquationalTheory.Soundness.Fill
open import EquationalTheory.Soundness.UnboxBeta
open import EquationalTheory.Soundness.Comm
open import EquationalTheory.Soundness.Handle
open import EquationalTheory.Soundness.HandlePerform

---- Soundness of the operational semantics

open import DenotationalSemantics.Soundness.Preservation.Base
open import DenotationalSemantics.Soundness.Preservation.Unbox
open import DenotationalSemantics.Soundness.Preservation.Step
open import DenotationalSemantics.Soundness.Preservation.Handle
open import DenotationalSemantics.Soundness.Preservation

---- Soundness of the pure top-level operational semantics

open import DenotationalSemantics.Soundness.TickLemmas
open import DenotationalSemantics.Soundness.TopLevelPure

---- Concrete time-ticks Kripke frames

open import DenotationalSemantics.Model.Example.World.LeftSidedIntervalsWithTicks
open import DenotationalSemantics.Model.Example.World.TwoSidedIntervalsWithTicks
open import DenotationalSemantics.Model.Example.World.TwoSidedIntervalsWithInfinityWithTicks
open import DenotationalSemantics.Model.Example.World.SetOfTracesWithTicks
open import DenotationalSemantics.Model.Example.World.SetOfTracesUpToSubtraceWithTicks

---- Concrete trace-history Kripke frames

open import DenotationalSemantics.Model.Example.World.TwoSidedIntervalsWithTraceHistories
open import DenotationalSemantics.Model.Example.World.TwoSidedIntervalsWithInfinityWithTraceHistories
open import DenotationalSemantics.Model.Example.World.SetOfTracesWithTraceHistories
open import DenotationalSemantics.Model.Example.World.SetOfTracesUpToSubtraceWithTraceHistories
