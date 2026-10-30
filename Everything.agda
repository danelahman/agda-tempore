------------------------------------------------------------------------
-- Every module of the polymorphic calculus and its type inference, with
-- the grades, the language and the utilities they share with the
-- monomorphic calculus (`MonomorphicCalculus/Everything.agda`).
-- `Results` is the overview of the main definitions and results. The
-- inference examples are checked apart, by `Examples.agda`.
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

---- The hints the solver reads

import Grades.Hints

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

---- Examples

import Language.Examples.SensorNode
import Language.Examples.SensorNode.Identity


-- POLYMORPHIC CALCULUS
-----------------------

---- Scopes, open grade expressions, types, program contexts and contexts,
---- substitutions, raw terms and run-time terms

import PolymorphicCalculus.Syntax.Contexts
import PolymorphicCalculus.Syntax.Contexts.Properties
import PolymorphicCalculus.Syntax.Grades
import PolymorphicCalculus.Syntax.Raw
import PolymorphicCalculus.Syntax.Raw.GradeSubstitution
import PolymorphicCalculus.Syntax.Run
import PolymorphicCalculus.Syntax.Run.Substitution
import PolymorphicCalculus.Syntax.Scopes
import PolymorphicCalculus.Syntax.GradeSubstitution
import PolymorphicCalculus.Syntax.Types

---- Hypotheses, entailment, quantified orderings and closed instances

import PolymorphicCalculus.Hypotheses
import PolymorphicCalculus.Hypotheses.Instances
import PolymorphicCalculus.Hypotheses.Quantified

---- The open type system, erasure to raw terms, substitution of grades and of
---- variables, renaming, conversion of context types, resource values,
---- inversion, and instantiation

import PolymorphicCalculus.Typing
import PolymorphicCalculus.Typing.Conversion
import PolymorphicCalculus.Typing.Erasure
import PolymorphicCalculus.Typing.GradeSubstitution
import PolymorphicCalculus.Typing.Instantiation
import PolymorphicCalculus.Typing.Inversion
import PolymorphicCalculus.Typing.Renaming
import PolymorphicCalculus.Typing.Resources
import PolymorphicCalculus.Typing.ScopeClosed
import PolymorphicCalculus.Typing.Substitution
import PolymorphicCalculus.Typing.Transport

---- Operational semantics: states, state typings, the reduction, type safety
---- and termination

import PolymorphicCalculus.OperationalSemantics.Reduction
import PolymorphicCalculus.OperationalSemantics.State
import PolymorphicCalculus.OperationalSemantics.Termination
import PolymorphicCalculus.OperationalSemantics.Termination.Reducibility
import PolymorphicCalculus.OperationalSemantics.TypeSafety

---- Constraints, their generation, soundness and completeness of
---- generation, solvers, principality, the concrete solver, and inference
---- for values in program contexts

import PolymorphicCalculus.Inference.Completeness
import PolymorphicCalculus.Inference.Constraints.Properties
import PolymorphicCalculus.Inference.Constraints.Satisfaction
import PolymorphicCalculus.Inference.Constraints.Schemes
import PolymorphicCalculus.Inference.Constraints.Syntax
import PolymorphicCalculus.Inference.Generate
import PolymorphicCalculus.Inference.Outcome
import PolymorphicCalculus.Inference.Principality
import PolymorphicCalculus.Inference.ScopeClosed
import PolymorphicCalculus.Inference.Solver
import PolymorphicCalculus.Inference.SolverImpl
import PolymorphicCalculus.Inference.SolverImpl.Canon
import PolymorphicCalculus.Inference.SolverImpl.Core.Decorate
import PolymorphicCalculus.Inference.SolverImpl.Core.For
import PolymorphicCalculus.Inference.SolverImpl.Core.Occurs
import PolymorphicCalculus.Inference.SolverImpl.Core.Rigid
import PolymorphicCalculus.Inference.SolverImpl.Core.Skel
import PolymorphicCalculus.Inference.SolverImpl.Core.SkelUnify
import PolymorphicCalculus.Inference.SolverImpl.Core.SkelUnifyMGU
import PolymorphicCalculus.Inference.SolverImpl.Core.SkelUnifySound
import PolymorphicCalculus.Inference.SolverImpl.Core.Thick
import PolymorphicCalculus.Inference.SolverImpl.Deferred
import PolymorphicCalculus.Inference.SolverImpl.Eliminate
import PolymorphicCalculus.Inference.SolverImpl.Entail
import PolymorphicCalculus.Inference.SolverImpl.Enum
import PolymorphicCalculus.Inference.SolverImpl.Expand
import PolymorphicCalculus.Inference.SolverImpl.Former
import PolymorphicCalculus.Inference.SolverImpl.Localise
import PolymorphicCalculus.Inference.SolverImpl.Localise.Closure
import PolymorphicCalculus.Inference.SolverImpl.Normal
import PolymorphicCalculus.Inference.SolverImpl.Polarity
import PolymorphicCalculus.Inference.SolverImpl.Principal
import PolymorphicCalculus.Inference.SolverImpl.Product
import PolymorphicCalculus.Inference.SolverImpl.Reach
import PolymorphicCalculus.Inference.SolverImpl.Resid
import PolymorphicCalculus.Inference.SolverImpl.RigidFree
import PolymorphicCalculus.Inference.SolverImpl.Search
import PolymorphicCalculus.Inference.SolverImpl.Simplify
import PolymorphicCalculus.Inference.SolverImpl.Solve
import PolymorphicCalculus.Inference.SolverImpl.State
import PolymorphicCalculus.Inference.SolverImpl.Strengthen
import PolymorphicCalculus.Inference.SolverImpl.Values
import PolymorphicCalculus.Inference.SolverImpl.Vars
import PolymorphicCalculus.Inference.Soundness
import PolymorphicCalculus.Inference.Values

---- Programs: their erasure, the substitution of definitions, the program
---- judgement, instantiation and the corollary for programs, and checking

import PolymorphicCalculus.Programs.Checking
import PolymorphicCalculus.Programs.Instantiation
import PolymorphicCalculus.Programs.Substitution
import PolymorphicCalculus.Programs.Syntax
import PolymorphicCalculus.Programs.Typing
