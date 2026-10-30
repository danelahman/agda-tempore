------------------------------------------------------------------------
-- Every module of the closed calculus. `ClosedCalculus.Results` is the
-- overview of its main definitions and results.
------------------------------------------------------------------------

module ClosedCalculus.Everything where

import ClosedCalculus.Results

---- Types, contexts, intrinsically typed terms, subtyping, renaming and
---- substitution, erasure and normal forms

import ClosedCalculus.Syntax.CompContext
import ClosedCalculus.Syntax.Contexts
import ClosedCalculus.Syntax.Data
import ClosedCalculus.Syntax.Data.Order
import ClosedCalculus.Syntax.Erasure
import ClosedCalculus.Syntax.Normalisation
import ClosedCalculus.Syntax.Renaming
import ClosedCalculus.Syntax.Renaming.Action
import ClosedCalculus.Syntax.Renaming.Base
import ClosedCalculus.Syntax.Renaming.Category
import ClosedCalculus.Syntax.Renaming.Coherence
import ClosedCalculus.Syntax.Renaming.Equivalence
import ClosedCalculus.Syntax.Substitution
import ClosedCalculus.Syntax.Substitution.Action
import ClosedCalculus.Syntax.Substitution.At
import ClosedCalculus.Syntax.Substitution.Base
import ClosedCalculus.Syntax.Substitution.Chain
import ClosedCalculus.Syntax.Substitution.ChainEquivalence
import ClosedCalculus.Syntax.Substitution.Clauses
import ClosedCalculus.Syntax.Substitution.Equivalence
import ClosedCalculus.Syntax.Substitution.Interchange
import ClosedCalculus.Syntax.Substitution.Laws
import ClosedCalculus.Syntax.Substitution.Lookup
import ClosedCalculus.Syntax.Substitution.Subsumption
import ClosedCalculus.Syntax.Substitution.Variables
import ClosedCalculus.Syntax.Subtyping
import ClosedCalculus.Syntax.Terms
import ClosedCalculus.Syntax.Terms.Equivalence
import ClosedCalculus.Syntax.Terms.Transport
import ClosedCalculus.Syntax.Types

---- Operational semantics: states, reduction, progress, termination, the
---- equivalence of states, the machine running operation implementations,
---- and soundness of the reduction for the denotational semantics

import ClosedCalculus.OperationalSemantics.Evaluation
import ClosedCalculus.OperationalSemantics.GradedReach
import ClosedCalculus.OperationalSemantics.Progress
import ClosedCalculus.OperationalSemantics.Reduction
import ClosedCalculus.OperationalSemantics.Soundness.Preservation
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Base
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Handle
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.HandleOpClause
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.HandleOpCont
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Step
import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Unbox
import ClosedCalculus.OperationalSemantics.Soundness.TickLemmas
import ClosedCalculus.OperationalSemantics.Soundness.TopLevel
import ClosedCalculus.OperationalSemantics.State
import ClosedCalculus.OperationalSemantics.StateEquivalence
import ClosedCalculus.OperationalSemantics.StateEquivalence.Bisimulation
import ClosedCalculus.OperationalSemantics.StateEquivalence.Core
import ClosedCalculus.OperationalSemantics.StateEquivalence.Extensions
import ClosedCalculus.OperationalSemantics.StateEquivalence.Replay
import ClosedCalculus.OperationalSemantics.Termination
import ClosedCalculus.OperationalSemantics.Termination.Bind
import ClosedCalculus.OperationalSemantics.Termination.Environment
import ClosedCalculus.OperationalSemantics.Termination.Environment.Action
import ClosedCalculus.OperationalSemantics.Termination.Environment.Cell
import ClosedCalculus.OperationalSemantics.Termination.Environment.Core
import ClosedCalculus.OperationalSemantics.Termination.Environment.Variables
import ClosedCalculus.OperationalSemantics.Termination.Handle
import ClosedCalculus.OperationalSemantics.Termination.Reducibility
import ClosedCalculus.OperationalSemantics.TopLevel
import ClosedCalculus.OperationalSemantics.TopLevel.Progress
import ClosedCalculus.OperationalSemantics.TopLevel.Reduction

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
import ClosedCalculus.Adequacy.Equational
import ClosedCalculus.Adequacy.HeadFaithful
import ClosedCalculus.Adequacy.PSh.HeadFaithful
import ClosedCalculus.Adequacy.PSh.TickFrames
import ClosedCalculus.Adequacy.PSh.TreeHead
import ClosedCalculus.Adequacy.PSh.TreeShape

---- Examples

import ClosedCalculus.DenotationalSemantics.Model.Example.World
import ClosedCalculus.Examples.Typing
