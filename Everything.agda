------------------------------------------------------------------------
-- Every module of the development except the type-inference examples
-- (`Examples`). `Results` is the overview of the main definitions and
-- results.
------------------------------------------------------------------------

module Everything where

import Results

-- UTILITIES
------------

import Util.Equality
import Util.NonNegativeRational


-- GRADES
---------

---- Grade algebras, grade morphisms and grade systems

import Grades.Base

---- Durations: the monoid of delays, time domains, intervals

import Grades.Durations
import Grades.Durations.Intervals
import Grades.Durations.Intervals.Dense
import Grades.Durations.Monus
import Grades.Durations.Nat
import Grades.Durations.NonNegativeRational
import Grades.Durations.Solver

---- Constructions on grades: products, upward closure, semidirect
---- products, indexed families

import Grades.Product
import Grades.Upward
import Grades.SemiDirect
import Grades.Indexed

---- Mode matrices

import Grades.Matrix
import Grades.Matrix.Boxes
import Grades.Matrix.Dioid
import Grades.Matrix.Fields
import Grades.Matrix.Matrices
import Grades.Matrix.ModeGrade
import Grades.Matrix.Modes
import Grades.Matrix.Nominal
import Grades.Matrix.Restrict

---- The timed-trace toolkit of the trace-based grades

import Grades.Traces
import Grades.Traces.Allowance
import Grades.Traces.Allowance.Antisym
import Grades.Traces.Allowance.AsOrder
import Grades.Traces.Allowance.Core
import Grades.Traces.Allowance.Decidable
import Grades.Traces.Allowance.Duration
import Grades.Traces.Allowance.Moves
import Grades.Traces.Allowance.ZeroCost
import Grades.Traces.Along
import Grades.Traces.Base
import Grades.Traces.Coverage
import Grades.Traces.Coverage.Antisym
import Grades.Traces.Coverage.AsOrder
import Grades.Traces.Coverage.Core
import Grades.Traces.Coverage.Decidable
import Grades.Traces.Coverage.Duration
import Grades.Traces.Coverage.Moves
import Grades.Traces.Durations
import Grades.Traces.Embedding
import Grades.Traces.Lexicographic
import Grades.Traces.MaxDuration
import Grades.Traces.MinDuration
import Grades.Traces.Order
import Grades.Traces.Positive
import Grades.Traces.Prefix
import Grades.Traces.Reduced
import Grades.Traces.Restriction
import Grades.Traces.RunConsistency
import Grades.Traces.RunConsistency.Cycles
import Grades.Traces.RunningTimes
import Grades.Traces.Sets
import Grades.Traces.Slack

---- Regular languages as grades

import Grades.Regular
import Grades.Regular.Automaton
import Grades.Regular.Basics
import Grades.Regular.Boolean
import Grades.Regular.Canonical
import Grades.Regular.Canonicity
import Grades.Regular.Closed
import Grades.Regular.Closure
import Grades.Regular.Coding
import Grades.Regular.Constructions
import Grades.Regular.Constructions.Base
import Grades.Regular.Constructions.Basic
import Grades.Regular.Constructions.Concatenation
import Grades.Regular.Constructions.Iteration
import Grades.Regular.Decide
import Grades.Regular.Determinise
import Grades.Regular.Explore
import Grades.Regular.Expression
import Grades.Regular.Grade
import Grades.Regular.Inclusion
import Grades.Regular.Literal
import Grades.Regular.Meet
import Grades.Regular.Moore
import Grades.Regular.Operations
import Grades.Regular.Plus
import Grades.Regular.Properties
import Grades.Regular.Reach

---- Exact timed words and interval-letter grades

import Grades.Exact
import Grades.Exact.Base
import Grades.Exact.Durations
import Grades.Exact.Expression
import Grades.Exact.Finite
import Grades.Exact.Finite.Durations
import Grades.Exact.Finite.Grades
import Grades.Exact.Finite.Interval
import Grades.Exact.Grid
import Grades.Exact.Grid.NonNegativeRational
import Grades.Exact.Hull
import Grades.Exact.Interval
import Grades.Exact.Joint
import Grades.Exact.Joint.Complete
import Grades.Exact.Joint.Decide
import Grades.Exact.Joint.Scale
import Grades.Exact.Joint.Zone
import Grades.Exact.Joint.Zoned
import Grades.Exact.Letters
import Grades.Exact.Lift
import Grades.Exact.NonRigid.Base
import Grades.Exact.NonRigid.Lower
import Grades.Exact.NonRigid.Upper
import Grades.Exact.Offsets
import Grades.Exact.Order
import Grades.Exact.Positions
import Grades.Exact.Pour
import Grades.Exact.Reader
import Grades.Exact.Reader.Lower
import Grades.Exact.Reader.Lower.Build
import Grades.Exact.Reader.Lower.Close
import Grades.Exact.Reader.Lower.Correct
import Grades.Exact.Reader.Lower.Family
import Grades.Exact.Reader.Lower.Mimic
import Grades.Exact.Reader.Lower.Read
import Grades.Exact.Reader.Lower.Zone
import Grades.Exact.Reader.Rename
import Grades.Exact.Reader.Transfer
import Grades.Exact.Reader.Upper
import Grades.Exact.Reader.Upper.Build
import Grades.Exact.Reader.Upper.Close
import Grades.Exact.Reader.Upper.Correct
import Grades.Exact.Reader.Upper.Family
import Grades.Exact.Reader.Upper.Mimic
import Grades.Exact.Reader.Upper.Read
import Grades.Exact.Reader.Upper.Zone
import Grades.Exact.Regular.Decide
import Grades.Exact.Regular.Durations
import Grades.Exact.Regular.Gap
import Grades.Exact.Regular.Grades
import Grades.Exact.Regular.Interval
import Grades.Exact.Regular.Lower
import Grades.Exact.Regular.Unroll
import Grades.Exact.Regular.Upper
import Grades.Exact.Regular.Words
import Grades.Exact.Resize
import Grades.Exact.Slots
import Grades.Exact.Splice

---- Examples

import Grades.Examples


-- LANGUAGE
-----------

import Language.BaseTypes
import Language.Comparisons
import Language.GroundTypes
import Language.Operations
import Language.Spec
import Language.Types

---- Examples

import Language.Examples.SensorNode
import Language.Examples.SensorNode.Identity


-- OPEN CALCULUS
----------------

---- Scopes, open grade expressions, types and contexts, substitutions, raw
---- terms

import OpenCalculus.Syntax.Contexts
import OpenCalculus.Syntax.ContextsLemmas
import OpenCalculus.Syntax.Grades
import OpenCalculus.Syntax.Raw
import OpenCalculus.Syntax.Raw.Subst
import OpenCalculus.Syntax.Scopes
import OpenCalculus.Syntax.Subst
import OpenCalculus.Syntax.Types

---- Hypotheses, entailment, obligations and closed instances

import OpenCalculus.Hypotheses
import OpenCalculus.Hypotheses.Instances
import OpenCalculus.Hypotheses.Obligations

---- The open type system, and erasure to raw terms

import OpenCalculus.Typing
import OpenCalculus.Typing.Erasure

---- Constraints, their generation, soundness and completeness of
---- generation, solvers, principality, and the concrete solver

import OpenCalculus.Inference.Completeness
import OpenCalculus.Inference.Constraints.Properties
import OpenCalculus.Inference.Constraints.Satisfaction
import OpenCalculus.Inference.Constraints.Syntax
import OpenCalculus.Inference.Generate
import OpenCalculus.Inference.Outcome
import OpenCalculus.Inference.Principality
import OpenCalculus.Inference.Solver
import OpenCalculus.Inference.SolverImpl
import OpenCalculus.Inference.SolverImpl.Canon
import OpenCalculus.Inference.SolverImpl.Core.Decorate
import OpenCalculus.Inference.SolverImpl.Core.For
import OpenCalculus.Inference.SolverImpl.Core.Occurs
import OpenCalculus.Inference.SolverImpl.Core.Rigid
import OpenCalculus.Inference.SolverImpl.Core.Skel
import OpenCalculus.Inference.SolverImpl.Core.SkelUnify
import OpenCalculus.Inference.SolverImpl.Core.SkelUnifyMGU
import OpenCalculus.Inference.SolverImpl.Core.SkelUnifySound
import OpenCalculus.Inference.SolverImpl.Core.Thick
import OpenCalculus.Inference.SolverImpl.Deferred
import OpenCalculus.Inference.SolverImpl.Eliminate
import OpenCalculus.Inference.SolverImpl.Entail
import OpenCalculus.Inference.SolverImpl.Enum
import OpenCalculus.Inference.SolverImpl.Expand
import OpenCalculus.Inference.SolverImpl.Former
import OpenCalculus.Inference.SolverImpl.Localise
import OpenCalculus.Inference.SolverImpl.Localise.Closure
import OpenCalculus.Inference.SolverImpl.Normal
import OpenCalculus.Inference.SolverImpl.Polarity
import OpenCalculus.Inference.SolverImpl.Principal
import OpenCalculus.Inference.SolverImpl.Product
import OpenCalculus.Inference.SolverImpl.Reach
import OpenCalculus.Inference.SolverImpl.Resid
import OpenCalculus.Inference.SolverImpl.RigidFree
import OpenCalculus.Inference.SolverImpl.Search
import OpenCalculus.Inference.SolverImpl.Simplify
import OpenCalculus.Inference.SolverImpl.Solve
import OpenCalculus.Inference.SolverImpl.State
import OpenCalculus.Inference.SolverImpl.Strengthen
import OpenCalculus.Inference.SolverImpl.Values
import OpenCalculus.Inference.SolverImpl.Vars
import OpenCalculus.Inference.Soundness


-- CLOSED CALCULUS
------------------

---- Contexts, intrinsically typed terms, subtyping, renamings and
---- substitutions, erasure and normal forms

import ClosedCalculus.Syntax.CompContext
import ClosedCalculus.Syntax.Contexts
import ClosedCalculus.Syntax.Data
import ClosedCalculus.Syntax.Data.Order
import ClosedCalculus.Syntax.Erasure
import ClosedCalculus.Syntax.Normalisation
import ClosedCalculus.Syntax.RenActions
import ClosedCalculus.Syntax.Renamings
import ClosedCalculus.Syntax.Renamings.Base
import ClosedCalculus.Syntax.Renamings.Category
import ClosedCalculus.Syntax.Renamings.Coherence
import ClosedCalculus.Syntax.Renamings.Equivalence
import ClosedCalculus.Syntax.Substitutions
import ClosedCalculus.Syntax.Substitutions.Action
import ClosedCalculus.Syntax.Substitutions.At
import ClosedCalculus.Syntax.Substitutions.Base
import ClosedCalculus.Syntax.Substitutions.Chain
import ClosedCalculus.Syntax.Substitutions.ChainEquivalence
import ClosedCalculus.Syntax.Substitutions.Clauses
import ClosedCalculus.Syntax.Substitutions.Equivalence
import ClosedCalculus.Syntax.Substitutions.Interchange
import ClosedCalculus.Syntax.Substitutions.Laws
import ClosedCalculus.Syntax.Substitutions.Lookup
import ClosedCalculus.Syntax.Substitutions.Subsumption
import ClosedCalculus.Syntax.Substitutions.Variables
import ClosedCalculus.Syntax.Subtyping
import ClosedCalculus.Syntax.Terms
import ClosedCalculus.Syntax.Terms.Equivalence
import ClosedCalculus.Syntax.Terms.Transport

---- Operational semantics: states, reduction, progress and preservation

import ClosedCalculus.OperationalSemantics.PreservationTheorem
import ClosedCalculus.OperationalSemantics.ProgressTheorem
import ClosedCalculus.OperationalSemantics.Soundness.Preservation
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Base
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Handle
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.HandleOpClause
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.HandleOpCont
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Step
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Unbox
import ClosedCalculus.OperationalSemantics.Soundness.TickLemmas
import ClosedCalculus.OperationalSemantics.Soundness.TopLevelPure
import ClosedCalculus.OperationalSemantics.State
import ClosedCalculus.OperationalSemantics.TopLevelOpSemantics
import ClosedCalculus.OperationalSemantics.TopLevelPreservationTheorem
import ClosedCalculus.OperationalSemantics.TopLevelProgressTheorem

---- Equational theory

import ClosedCalculus.EquationalTheory.Alignment
import ClosedCalculus.EquationalTheory.EquationalTheory
import ClosedCalculus.EquationalTheory.Naturality
import ClosedCalculus.EquationalTheory.Soundness
import ClosedCalculus.EquationalTheory.Soundness.Base
import ClosedCalculus.EquationalTheory.Soundness.Coerce
import ClosedCalculus.EquationalTheory.Soundness.Comm
import ClosedCalculus.EquationalTheory.Soundness.Delay
import ClosedCalculus.EquationalTheory.Soundness.Fill
import ClosedCalculus.EquationalTheory.Soundness.Handle
import ClosedCalculus.EquationalTheory.Soundness.HandlePerform
import ClosedCalculus.EquationalTheory.Soundness.Modal
import ClosedCalculus.EquationalTheory.Soundness.Parametric
import ClosedCalculus.EquationalTheory.Soundness.Seq
import ClosedCalculus.EquationalTheory.Soundness.SeqAssoc
import ClosedCalculus.EquationalTheory.Soundness.UnboxBeta
import ClosedCalculus.EquationalTheory.Soundness.Values

---- Denotational semantics: the abstract model, the presheaf model, the
---- interpretation

import ClosedCalculus.DenotationalSemantics.Interpretation.Comparisons
import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts
import ClosedCalculus.DenotationalSemantics.Interpretation.Data
import ClosedCalculus.DenotationalSemantics.Interpretation.Recursion
import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming
import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Algebra
import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Extension
import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Structural
import ClosedCalculus.DenotationalSemantics.Interpretation.RenamingCoherence
import ClosedCalculus.DenotationalSemantics.Interpretation.State
import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence
import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Base
import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Core
import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Env
import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport
import ClosedCalculus.DenotationalSemantics.Interpretation.Subtyping
import ClosedCalculus.DenotationalSemantics.Interpretation.Terms
import ClosedCalculus.DenotationalSemantics.Interpretation.Types
import ClosedCalculus.DenotationalSemantics.Interpretation.Variables
import ClosedCalculus.DenotationalSemantics.Model.Category
import ClosedCalculus.DenotationalSemantics.Model.Comparison
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Base
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.GroundTypes
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Implementation
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Eternal
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Effects
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Laws
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Mu
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Instance
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.TickMonad
import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.TopLevelInstance
import ClosedCalculus.DenotationalSemantics.Model.GroundEternal
import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
import ClosedCalculus.DenotationalSemantics.Model.Implementation
import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
import ClosedCalculus.DenotationalSemantics.Model.Modality.Eternal
import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
import ClosedCalculus.DenotationalSemantics.Model.Monad
import ClosedCalculus.DenotationalSemantics.Model.Monad.Enrichment
import ClosedCalculus.DenotationalSemantics.Model.TickMonad
import ClosedCalculus.DenotationalSemantics.Model.World
import ClosedCalculus.DenotationalSemantics.Model.World.Action
import ClosedCalculus.DenotationalSemantics.Model.World.History
import ClosedCalculus.DenotationalSemantics.Model.World.Product
import ClosedCalculus.DenotationalSemantics.Model.World.Reindex

---- Adequacy of the denotational semantics

import ClosedCalculus.Adequacy.Adequacy
import ClosedCalculus.Adequacy.Bind
import ClosedCalculus.Adequacy.Environment
import ClosedCalculus.Adequacy.Environment.Action
import ClosedCalculus.Adequacy.Environment.Cell
import ClosedCalculus.Adequacy.Environment.Core
import ClosedCalculus.Adequacy.Environment.Variables
import ClosedCalculus.Adequacy.Equational
import ClosedCalculus.Adequacy.Evaluation
import ClosedCalculus.Adequacy.GradedReach
import ClosedCalculus.Adequacy.Handle
import ClosedCalculus.Adequacy.HeadFaithful
import ClosedCalculus.Adequacy.Normalization
import ClosedCalculus.Adequacy.PSh.HeadFaithful
import ClosedCalculus.Adequacy.PSh.TickFrames
import ClosedCalculus.Adequacy.PSh.TreeHead
import ClosedCalculus.Adequacy.PSh.TreeShape
import ClosedCalculus.Adequacy.Reducibility
import ClosedCalculus.Adequacy.StateEquivalence
import ClosedCalculus.Adequacy.StateEquivalence.Bisimulation
import ClosedCalculus.Adequacy.StateEquivalence.Core
import ClosedCalculus.Adequacy.StateEquivalence.Extensions
import ClosedCalculus.Adequacy.StateEquivalence.Replay

---- Examples

import ClosedCalculus.DenotationalSemantics.Model.Example.World
import ClosedCalculus.Examples.Typing


-- BRIDGE BETWEEN THE CALCULI
-----------------------------

---- Instantiation: open typings as families of declarative typings, and
---- soundness and completeness of inference for the declarative system

import Bridge.Instantiation.Completeness
import Bridge.Instantiation.Correspondence
import Bridge.Instantiation.Embedding
import Bridge.Instantiation.Inference
import Bridge.Instantiation.Judgements
import Bridge.Instantiation.Terms
import Bridge.Instantiation.Types


-- The inference examples, and the completeness example relating the two
-- calculi, are checked separately (`make examples`).
