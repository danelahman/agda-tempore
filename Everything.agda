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

---- Substitutions: the generating calculus, and replacing one variable as a
---- notation for it

open import Syntax.Substitutions.Base
open import Syntax.Substitutions.Lookup
open import Syntax.Substitutions.Action
open import Syntax.Substitutions

---- Equivalence of renamings, of terms, and coherence of the action

open import Syntax.Renamings.Equivalence
open import Syntax.Terms.Equivalence
open import Syntax.Renamings.Coherence
open import Syntax.Renamings.Category
open import Syntax.Terms.Transport

---- Substitutions: composition, the quotient, and the laws

open import Syntax.Substitutions.Equivalence
open import Syntax.Substitutions.Chain
open import Syntax.Substitutions.Interchange
open import Syntax.Substitutions.ChainEquivalence
open import Syntax.Substitutions.Restrict
open import Syntax.Substitutions.Laws

---- Substituting at a context's prefix boundary, which is the form every
---- consumer uses

open import Syntax.Substitutions.Variables
open import Syntax.Substitutions.At
open import Syntax.Substitutions.Clauses

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

---- The syntactic equivalence is contained in the equational theory

open import EquationalTheory.Alignment

---- Equational theory's soundness theorem

open import EquationalTheory.Soundness


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
open import DenotationalSemantics.Interpretation.Renaming.Algebra
open import DenotationalSemantics.Interpretation.Renaming.Extension
open import DenotationalSemantics.Interpretation.Renaming.Structural
open import DenotationalSemantics.Interpretation.Renaming
open import DenotationalSemantics.Interpretation.RenamingCoherence
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Unbox
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Core
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

open import OperationalSemantics.Soundness.Preservation.Base
open import OperationalSemantics.Soundness.Preservation.Unbox
open import OperationalSemantics.Soundness.Preservation.Step
open import OperationalSemantics.Soundness.Preservation.Handle
open import OperationalSemantics.Soundness.Preservation

---- Soundness of the pure top-level operational semantics

open import OperationalSemantics.Soundness.TickLemmas
open import OperationalSemantics.Soundness.TopLevelPure

---- Adequacy of the interpretation with respect to the operational semantics

open import OperationalSemantics.Adequacy.Evaluation
open import OperationalSemantics.Adequacy.StateEquivalence.Core
open import OperationalSemantics.Adequacy.StateEquivalence.Extensions
open import OperationalSemantics.Adequacy.StateEquivalence.Bisimulation
open import OperationalSemantics.Adequacy.StateEquivalence.Replay
open import OperationalSemantics.Adequacy.StateEquivalence
open import OperationalSemantics.Adequacy.GradedReach
open import OperationalSemantics.Adequacy.Reducibility
open import OperationalSemantics.Adequacy.Environment.Core
open import OperationalSemantics.Adequacy.Environment.Action
open import OperationalSemantics.Adequacy.Environment.Variables
open import OperationalSemantics.Adequacy.Environment.Clauses
open import OperationalSemantics.Adequacy.Environment.Cell
open import OperationalSemantics.Adequacy.Environment
open import OperationalSemantics.Adequacy.Bind
open import OperationalSemantics.Adequacy.Handle
open import OperationalSemantics.Adequacy.Normalization
open import OperationalSemantics.Adequacy.HeadFaithful
open import OperationalSemantics.Adequacy.Adequacy

---- Head shapes of effect trees in the presheaf model

open import OperationalSemantics.Adequacy.PSh.TreeShape
open import OperationalSemantics.Adequacy.PSh.TreeHead
open import OperationalSemantics.Adequacy.PSh.HeadFaithful
open import OperationalSemantics.Adequacy.PSh.TickFrames

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
