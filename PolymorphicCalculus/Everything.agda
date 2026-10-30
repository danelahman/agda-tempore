------------------------------------------------------------------------
-- Every module of the polymorphic calculus and its type inference.
-- `PolymorphicCalculus/Results.agda` is the overview of its main results.
-- Check with `agda PolymorphicCalculus/Everything.agda`; the inference
-- examples are checked apart, by `agda PolymorphicCalculus/Examples.agda`.
------------------------------------------------------------------------

module PolymorphicCalculus.Everything where

import PolymorphicCalculus.Results

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
