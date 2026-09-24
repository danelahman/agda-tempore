--------------------------------------------------------------------------
-- Agda formalisation of the syntax and semantics of a core language    --
-- for programming with temporal resources using modal types.           --
--                                                                      --
-- The language has:                                                    --
--                                                                      --
--   - a modality on types that specifies that data might not yet be    --
--     available, but will be once a resource grade ρ has elapsed      --
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
--   - constraint-based type inference: a mirrored type system with     --
--     type and grade variables, constraint generation for raw terms,   --
--     its soundness and completeness, principal typings relative to    --
--     an axiomatised constraint solver, and a concrete solver with     --
--     the simplified report of its answer                              --
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

---- Substituting at a context's prefix boundary, which is the form every
---- consumer uses

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

---- Grades, grade morphisms, and grade systems

open import Syntax.Grades

---- The timed-trace toolkit the trace-based grades are built from
---- (see the module for how its pieces fit together)

import Syntax.Grades.Traces

---- Example grades and grade systems: time intervals, sets of timed
---- traces, and the projections pairing them up
---- (see the module for what each example is and how they relate)

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

---- Concrete Kripke frames: time-ticks worlds and trace-history worlds,
---- one of each per example grade, and the frames each grade system is
---- modelled over
---- (see the module for the contrast between the two families)

import DenotationalSemantics.Model.Example.World


-- TYPE INFERENCE
-----------------

---- Scopes of type and grade variables

open import TypeInference.Scopes

---- Open grade expressions, types, and contexts (with the eternal barrier)

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

---- The mirrored qualified type system

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

---- Axiomatised constraint solvers, principal types and principal typings

open import TypeInference.Outcome
open import TypeInference.Solver
open import TypeInference.Principality

---- Semantic refutation of a grade ordering against the unit, and the
---- settling of reported var-rule disjunctions it justifies

import TypeInference.SolverImpl.Refute
import TypeInference.SolverImpl.Simplify

---- Polarity-directed elimination of an unknown at the reporting
---- boundary, fixing the image of the program's variables, and the
---- product normal form of what is left

import TypeInference.SolverImpl.Vars
import TypeInference.SolverImpl.Eliminate
import TypeInference.SolverImpl.Product
import TypeInference.SolverImpl.Canon

---- Deferred rigid conditions: a clause's orderings mixing its rigid
---- with outer unknowns, kept under their binders

import TypeInference.SolverImpl.Deferred

---- The rigid-binder-free fragment

import TypeInference.SolverImpl.RigidFree

---- What the solver's variable expansion buys: decomposability of every
---- expanded demand, most-generality of the expansion, and refutation

import TypeInference.SolverImpl.Expand

---- The solver's principality and refutation, the atoms of its residue
---- that no unknown affects decided, the report strengthened to the
---- variables occurring in it or in the image of the program's
---- variables, the solver itself, and inference: a principal typing

import TypeInference.SolverImpl.Principal
import TypeInference.SolverImpl.Closed
import TypeInference.SolverImpl.Strengthen
import TypeInference.SolverImpl
