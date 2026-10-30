------------------------------------------------------------------------
-- Every module of the monomorphic calculus.
-- `MonomorphicCalculus.Results` is the overview of its main definitions
-- and results.
------------------------------------------------------------------------

module MonomorphicCalculus.Everything where

import MonomorphicCalculus.Results

---- Types, contexts, intrinsically typed terms, subtyping, renaming and
---- substitution, erasure and normal forms

import MonomorphicCalculus.Syntax.CompContext
import MonomorphicCalculus.Syntax.Contexts
import MonomorphicCalculus.Syntax.Data
import MonomorphicCalculus.Syntax.Data.Order
import MonomorphicCalculus.Syntax.Erasure
import MonomorphicCalculus.Syntax.Normalisation
import MonomorphicCalculus.Syntax.Renaming
import MonomorphicCalculus.Syntax.Renaming.Action
import MonomorphicCalculus.Syntax.Renaming.Base
import MonomorphicCalculus.Syntax.Renaming.Category
import MonomorphicCalculus.Syntax.Renaming.Coherence
import MonomorphicCalculus.Syntax.Renaming.Equivalence
import MonomorphicCalculus.Syntax.Substitution
import MonomorphicCalculus.Syntax.Substitution.Action
import MonomorphicCalculus.Syntax.Substitution.At
import MonomorphicCalculus.Syntax.Substitution.Base
import MonomorphicCalculus.Syntax.Substitution.Chain
import MonomorphicCalculus.Syntax.Substitution.ChainEquivalence
import MonomorphicCalculus.Syntax.Substitution.Clauses
import MonomorphicCalculus.Syntax.Substitution.Equivalence
import MonomorphicCalculus.Syntax.Substitution.Interchange
import MonomorphicCalculus.Syntax.Substitution.Laws
import MonomorphicCalculus.Syntax.Substitution.Lookup
import MonomorphicCalculus.Syntax.Substitution.Subsumption
import MonomorphicCalculus.Syntax.Substitution.Variables
import MonomorphicCalculus.Syntax.Subtyping
import MonomorphicCalculus.Syntax.Terms
import MonomorphicCalculus.Syntax.Terms.Equivalence
import MonomorphicCalculus.Syntax.Terms.Transport
import MonomorphicCalculus.Syntax.Types

---- Operational semantics: states, reduction, progress, termination, the
---- equivalence of states, the machine running operation implementations,
---- and soundness of the reduction for the denotational semantics

import MonomorphicCalculus.OperationalSemantics.Evaluation
import MonomorphicCalculus.OperationalSemantics.GradedReach
import MonomorphicCalculus.OperationalSemantics.Progress
import MonomorphicCalculus.OperationalSemantics.Reduction
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Base
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Handle
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.HandleOpClause
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.HandleOpCont
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Step
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Unbox
import MonomorphicCalculus.OperationalSemantics.Soundness.TickLemmas
import MonomorphicCalculus.OperationalSemantics.Soundness.TopLevel
import MonomorphicCalculus.OperationalSemantics.State
import MonomorphicCalculus.OperationalSemantics.StateEquivalence
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Bisimulation
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Core
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Extensions
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Replay
import MonomorphicCalculus.OperationalSemantics.Termination
import MonomorphicCalculus.OperationalSemantics.Termination.Bind
import MonomorphicCalculus.OperationalSemantics.Termination.Environment
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Action
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Cell
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Core
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Variables
import MonomorphicCalculus.OperationalSemantics.Termination.Handle
import MonomorphicCalculus.OperationalSemantics.Termination.Reducibility
import MonomorphicCalculus.OperationalSemantics.TopLevel
import MonomorphicCalculus.OperationalSemantics.TopLevel.Progress
import MonomorphicCalculus.OperationalSemantics.TopLevel.Reduction

---- Equational theory

import MonomorphicCalculus.EquationalTheory.Alignment
import MonomorphicCalculus.EquationalTheory.EquationalTheory
import MonomorphicCalculus.EquationalTheory.Naturality
import MonomorphicCalculus.EquationalTheory.Soundness
import MonomorphicCalculus.EquationalTheory.Soundness.Base
import MonomorphicCalculus.EquationalTheory.Soundness.Coerce
import MonomorphicCalculus.EquationalTheory.Soundness.Comm
import MonomorphicCalculus.EquationalTheory.Soundness.Delay
import MonomorphicCalculus.EquationalTheory.Soundness.Fill
import MonomorphicCalculus.EquationalTheory.Soundness.Handle
import MonomorphicCalculus.EquationalTheory.Soundness.HandlePerform
import MonomorphicCalculus.EquationalTheory.Soundness.Modal
import MonomorphicCalculus.EquationalTheory.Soundness.Parametric
import MonomorphicCalculus.EquationalTheory.Soundness.Seq
import MonomorphicCalculus.EquationalTheory.Soundness.SeqAssoc
import MonomorphicCalculus.EquationalTheory.Soundness.UnboxBeta
import MonomorphicCalculus.EquationalTheory.Soundness.Values

---- Denotational semantics: the abstract model, the presheaf model, the
---- interpretation

import MonomorphicCalculus.DenotationalSemantics.Interpretation.Comparisons
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Data
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Recursion
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming.Algebra
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming.Extension
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming.Structural
import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence
import MonomorphicCalculus.DenotationalSemantics.Interpretation.State
import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence
import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Base
import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Core
import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Env
import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types
import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables
import MonomorphicCalculus.DenotationalSemantics.Model.Category
import MonomorphicCalculus.DenotationalSemantics.Model.Comparison
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Implementation
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Eternal
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Effects
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Laws
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Mu
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Instance
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.TickMonad
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.TopLevelInstance
import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Implementation
import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
import MonomorphicCalculus.DenotationalSemantics.Model.Monad
import MonomorphicCalculus.DenotationalSemantics.Model.Monad.Enrichment
import MonomorphicCalculus.DenotationalSemantics.Model.TickMonad
import MonomorphicCalculus.DenotationalSemantics.Model.World
import MonomorphicCalculus.DenotationalSemantics.Model.World.Action
import MonomorphicCalculus.DenotationalSemantics.Model.World.History
import MonomorphicCalculus.DenotationalSemantics.Model.World.Product
import MonomorphicCalculus.DenotationalSemantics.Model.World.Reindex

---- Adequacy of the denotational semantics

import MonomorphicCalculus.Adequacy.Adequacy
import MonomorphicCalculus.Adequacy.Equational
import MonomorphicCalculus.Adequacy.HeadFaithful
import MonomorphicCalculus.Adequacy.PSh.HeadFaithful
import MonomorphicCalculus.Adequacy.PSh.TickFrames
import MonomorphicCalculus.Adequacy.PSh.TreeHead
import MonomorphicCalculus.Adequacy.PSh.TreeShape

---- Examples

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World
import MonomorphicCalculus.Examples.Typing
