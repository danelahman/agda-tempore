--------------------------------------------------------------------------
-- Agda formalisation of the syntax and semantics of a core language    --
-- for programming with temporal resources using modal types.           --
--                                                                      --
-- The language has:                                                    --
--                                                                      --
--   - a modality on types that specifies that data might not yet be    --
--     available, but will be once a resource grade ρ has elapsed       --
--                                                                      --
--   - a modality on contexts describing that a resource grade has      --
--     elapsed (allowing new data to become available)                  --
--                                                                      --
--   - features facilitating the interaction of these two modalities    --
--     based on adjunctions (i.e., Fitch-style modal type systems)      --
--                                                                      --
--   - computational effects modelled using algebraic operations with   --
--     prescribed effect grades, whose execution makes those grades     --
--     elapse (both in the semantics and in the static typing rules)    --
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
--                                                                      --
--   - soundness of the equational theory with respect to the           --
--     denotational semantics                                           --
--                                                                      --
--   - adequacy of the denotational semantics with respect to the       --
--     operational semantics, and for the equational theory             --
--                                                                      --
--   - constraint-based type inference: an open type system with type   --
--     and grade variables, constraint generation for raw terms and its --
--     soundness and completeness, principal type schemes relative to   --
--     an axiomatised constraint solver, and a concrete solver with a   --
--     simplified report of its solutions                               --
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

---- Shape-preserving subtyping of value and computation types

open import Syntax.Subtyping

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
open import Syntax.Substitutions.Laws

---- Subsumption for contexts

open import Syntax.Substitutions.Subsumption

---- Substitution at a context's prefix boundary

open import Syntax.Substitutions.Variables
open import Syntax.Substitutions.At
open import Syntax.Substitutions.Clauses

---- Computation term and evaluation contexts

open import Syntax.CompContext

---- Erasure to raw terms, and the theorem that subsumption is confined to
---- the reconciliation points

open import Syntax.Erasure
open import Syntax.Normalisation


-- GRADES
---------

---- Durations: the monoid of delays, its morphisms, stepped durations,
---- and the natural numbers as durations

open import Syntax.Durations
open import Syntax.Durations.Nat
open import Syntax.Durations.NonNegativeRational

---- Grades, grade morphisms, and grade systems

open import Syntax.Grades

---- The product of two grades, and of two grade systems

import Syntax.Grades.Product

---- The timed-trace toolkit of the trace-based grades

import Syntax.Grades.Traces

---- Regular languages as grades: canonical minimal automata, inclusion,
---- and extended regular-expression literals

import Syntax.Grades.Regular

---- Example grades and grade systems: time, sets of timed traces, counts,
---- security levels and their products, and the projections between them

import Syntax.Grades.Example

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

---- Naturality of subsumption, where the theory derives it

open import EquationalTheory.Naturality

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

---- Constructions on Kripke frames: products, reindexing, and the
---- action frame of a grade with its forward restriction

import DenotationalSemantics.Model.World.Product
import DenotationalSemantics.Model.World.Reindex
import DenotationalSemantics.Model.World.Action

---- Concrete model on setoid-valued presheaves over the worlds

open import DenotationalSemantics.Model.Example.PSh.Base
open import DenotationalSemantics.Model.Example.PSh.Modality.Future
open import DenotationalSemantics.Model.Example.PSh.Modality.Past
open import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction
open import DenotationalSemantics.Model.Example.PSh.Modality.Eternal
open import DenotationalSemantics.Model.Example.PSh.GroundTypes
open import DenotationalSemantics.Model.Example.PSh.Monad.Core
open import DenotationalSemantics.Model.Example.PSh.Monad.Effects
open import DenotationalSemantics.Model.Example.PSh.Monad.Handling
open import DenotationalSemantics.Model.Example.PSh.Monad.Instance
open import DenotationalSemantics.Model.Example.PSh.TickMonad
open import DenotationalSemantics.Model.Example.PSh.Implementation
open import DenotationalSemantics.Model.Example.PSh.TopLevelInstance

---- Interpretation of the calculus

open import DenotationalSemantics.Interpretation.Types
open import DenotationalSemantics.Interpretation.Subtyping
open import DenotationalSemantics.Interpretation.Contexts
open import DenotationalSemantics.Interpretation.Variables
open import DenotationalSemantics.Interpretation.Terms
open import DenotationalSemantics.Interpretation.Renaming.Algebra
open import DenotationalSemantics.Interpretation.Renaming.Extension
open import DenotationalSemantics.Interpretation.Renaming.Structural
open import DenotationalSemantics.Interpretation.Renaming
open import DenotationalSemantics.Interpretation.RenamingCoherence
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Env
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
open import OperationalSemantics.Adequacy.Environment.Cell
open import OperationalSemantics.Adequacy.Environment
open import OperationalSemantics.Adequacy.Bind
open import OperationalSemantics.Adequacy.Handle
open import OperationalSemantics.Adequacy.Normalization
open import OperationalSemantics.Adequacy.HeadFaithful
open import OperationalSemantics.Adequacy.Adequacy

---- Adequacy for the equational theory

open import OperationalSemantics.Adequacy.Equational

---- Head shapes of effect trees in the presheaf model

open import OperationalSemantics.Adequacy.PSh.TreeShape
open import OperationalSemantics.Adequacy.PSh.TreeHead
open import OperationalSemantics.Adequacy.PSh.HeadFaithful
open import OperationalSemantics.Adequacy.PSh.TickFrames

---- Concrete Kripke frames for the example grades: tick, tally, label and
---- trace-history worlds, and their products

import DenotationalSemantics.Model.Example.World


-- TYPE INFERENCE
-----------------

---- Scopes of type and grade variables

open import TypeInference.Scopes

---- Open grade expressions, types and contexts

open import TypeInference.OpenSyntax.Grades
open import TypeInference.OpenSyntax.Types
open import TypeInference.OpenSyntax.Contexts
open import TypeInference.OpenSyntax.ContextsLemmas

---- Substitutions between scopes

open import TypeInference.OpenSyntax.Subst

---- Hypothesis sets, entailment and subtyping of open types

open import TypeInference.OpenSyntax.Hyps

---- Closed instances: values of closed grades, closed decisions

open import TypeInference.OpenSyntax.Instances

---- The open type system

open import TypeInference.OpenSyntax.Language

---- Raw terms and erasure

open import TypeInference.Raw.Syntax
open import TypeInference.Raw.Subst
open import TypeInference.Erase

---- Constraints and their satisfaction

open import TypeInference.Constraints.Syntax
open import TypeInference.Constraints.Satisfaction
open import TypeInference.Constraints.Properties

---- Constraint generation

open import TypeInference.Generate

---- Soundness and completeness of constraint generation

open import TypeInference.Soundness
open import TypeInference.Completeness

---- Axiomatised constraint solvers, principal types and principal type
---- schemes

open import TypeInference.Outcome
open import TypeInference.Solver
open import TypeInference.Principality

---- Type formers and the variance of their parts: the table every
---- decomposition, traversal and recursion along a type reads

import TypeInference.SolverImpl.Former

---- Entailment of grade orderings from hypotheses at explicit strengths,
---- the closed check and refutation against the unit, and simplification
---- of reported hypothesis sets

import TypeInference.SolverImpl.Normal
import TypeInference.SolverImpl.Entail
import TypeInference.SolverImpl.Simplify

---- Sets of variables, the value rules for an unknown, polarity-based
---- elimination of unknowns from a report, and normal forms of grade
---- expressions

import TypeInference.SolverImpl.Vars
import TypeInference.SolverImpl.Values
import TypeInference.SolverImpl.Eliminate
import TypeInference.SolverImpl.Product
import TypeInference.SolverImpl.Canon

---- Reachability in a finite graph, by Warshall's algorithm, and cycle
---- elimination

import TypeInference.SolverImpl.Reach

---- Deferred rigid conditions: the orderings of a clause that mention its
---- rigid and outer unknowns, kept under their binders

import TypeInference.SolverImpl.Deferred

---- The rigid-binder-free fragment

import TypeInference.SolverImpl.RigidFree

---- Properties of variable expansion: decomposability of every expanded
---- demand, most-generality of the expansion, and refutation

import TypeInference.SolverImpl.Expand

---- Principality and refutation for the driver, strengthening of the
---- report, and the solver and inference

import TypeInference.SolverImpl.Principal
import TypeInference.SolverImpl.Strengthen
import TypeInference.SolverImpl

---- The inference examples are checked separately, with
---- `agda TypeInference/Examples.agda`

-- import TypeInference.Examples
