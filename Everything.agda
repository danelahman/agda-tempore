------------------------------------------------------------------------
-- Every module of the calculus with type and grade variables and its
-- type inference, with the grades, the language and the utilities they
-- share with the closed calculus (`ClosedCalculus/Everything.agda`).
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


-- OPEN CALCULUS
----------------

---- Scopes, open grade expressions, types, program contexts and contexts,
---- substitutions, raw terms and run-time terms

import OpenCalculus.Syntax.Contexts
import OpenCalculus.Syntax.Contexts.Properties
import OpenCalculus.Syntax.Grades
import OpenCalculus.Syntax.Raw
import OpenCalculus.Syntax.Raw.GradeSubstitution
import OpenCalculus.Syntax.Run
import OpenCalculus.Syntax.Run.Substitution
import OpenCalculus.Syntax.Scopes
import OpenCalculus.Syntax.GradeSubstitution
import OpenCalculus.Syntax.Types

---- Hypotheses, entailment, quantified orderings and closed instances

import OpenCalculus.Hypotheses
import OpenCalculus.Hypotheses.Instances
import OpenCalculus.Hypotheses.Quantified

---- The open type system, erasure to raw terms, substitution of grades and of
---- variables, renaming, conversion of context types, resource values,
---- inversion, and instantiation

import OpenCalculus.Typing
import OpenCalculus.Typing.Conversion
import OpenCalculus.Typing.Erasure
import OpenCalculus.Typing.GradeSubstitution
import OpenCalculus.Typing.Instantiation
import OpenCalculus.Typing.Inversion
import OpenCalculus.Typing.Renaming
import OpenCalculus.Typing.Resources
import OpenCalculus.Typing.ScopeClosed
import OpenCalculus.Typing.Substitution
import OpenCalculus.Typing.Transport

---- Operational semantics: states, state typings, the reduction, type safety
---- and termination

import OpenCalculus.OperationalSemantics.Reduction
import OpenCalculus.OperationalSemantics.State
import OpenCalculus.OperationalSemantics.Termination
import OpenCalculus.OperationalSemantics.Termination.Reducibility
import OpenCalculus.OperationalSemantics.TypeSafety

---- Constraints, their generation, soundness and completeness of
---- generation, solvers, principality, the concrete solver, and inference
---- for values in program contexts

import OpenCalculus.Inference.Completeness
import OpenCalculus.Inference.Constraints.Properties
import OpenCalculus.Inference.Constraints.Satisfaction
import OpenCalculus.Inference.Constraints.Schemes
import OpenCalculus.Inference.Constraints.Syntax
import OpenCalculus.Inference.Generate
import OpenCalculus.Inference.Outcome
import OpenCalculus.Inference.Principality
import OpenCalculus.Inference.ScopeClosed
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
import OpenCalculus.Inference.Values

---- Programs: their erasure, the substitution of definitions, the program
---- judgement, instantiation and the corollary for programs, and checking

import OpenCalculus.Programs.Checking
import OpenCalculus.Programs.Instantiation
import OpenCalculus.Programs.Substitution
import OpenCalculus.Programs.Syntax
import OpenCalculus.Programs.Typing
