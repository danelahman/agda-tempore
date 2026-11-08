------------------------------------------------------------------------
-- The monomorphic calculus                                           --
--                                                                    --
-- Every module of the monomorphic calculus: its syntax, operational  --
-- semantics and type safety, termination, equational theory,         --
-- denotational semantics with soundness and adequacy, and examples.  --
--                                                                    --
-- The calculus is parameterised by a language specification          --
-- (`LanguageSpec`, in `Language/Spec`): a grade system, base types   --
-- and operations signature.                                          --
--                                                                    --
-- Module paths below are relative to `MonomorphicCalculus/`.         --
--                                                                    --
-- Check with `agda MonomorphicCalculus/Everything.agda`.             --
------------------------------------------------------------------------

module MonomorphicCalculus.Everything where

------------------------------------------------------------------------
-- Syntax                                                             --
------------------------------------------------------------------------

-- Types, contexts and terms. A context lists variables and modalities
-- `⟨ ρ ⟩`, which are formalisation's notation for Fitch-style locks.
--
-- Where to look
--   Syntax/Types      value, computation and ground types, among them the
--                     handler types `C ⇛ D` (VType, CType, GType); eternal
--                     types (Et); the side condition of the variable rule
--                     (_Et∨≾ᵘ_)
--   Syntax/Contexts   contexts, their grade, and variables under modalities
--                     (Ctx, ctx-grade, _∈[_]_)
--   Syntax/Subtyping  subtyping of value and computation types (_<:ᵛ_, _<:ᶜ_)
--   Syntax/Terms      intrinsically typed values and computations (_⊢ᵛ⦂_,
--                     _⊢ᶜ⦂_); `handle M with H in N` stands for
--                     `handle M with handler N H` (handle_`with_`in_)
--   Syntax/Data       the data of a type and their structural order
--   Syntax/Erasure    erasure to raw terms

import MonomorphicCalculus.Syntax.CompContext
import MonomorphicCalculus.Syntax.Contexts
import MonomorphicCalculus.Syntax.Data
import MonomorphicCalculus.Syntax.Data.Order
import MonomorphicCalculus.Syntax.Erasure
import MonomorphicCalculus.Syntax.Subtyping
import MonomorphicCalculus.Syntax.Terms
import MonomorphicCalculus.Syntax.Terms.Equivalence
import MonomorphicCalculus.Syntax.Terms.Transport
import MonomorphicCalculus.Syntax.Types

------------------------------------------------------------------------
-- Renaming and substitution                                          --
------------------------------------------------------------------------

-- Renamings are built from weakening, exchange, variables and the renamings
-- concerning modalities. Substitutions are defined in their parallel form.
--
-- Where to look
--   Syntax/Renaming/Base             renamings and their generators (Ren,
--                                    wk-ren, exch-ren, var-ren, ⟨⟩-η-ren,
--                                    ⟨⟩-μ-ren, ⟨⟩-≤-ren, …)
--   Syntax/Renaming/Action           the action on terms (V-rename, C-rename)
--   Syntax/Substitution/Base         parallel substitutions
--   Syntax/Substitution              substitution for a variable, and for the
--                                    last two bound variables (_[_↦_]v,
--                                    _[_↦_]c, _[_]₀, _[_]₁)
--   Syntax/Substitution/Subsumption  context subsumption (subCtx)
--   Syntax/Normalisation             subsumption confined to the
--                                    reconciliation points

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

------------------------------------------------------------------------
-- Operational semantics                                              --
------------------------------------------------------------------------

-- A small-step reduction relation `⟨ 𝕊 ∣ M ⟩⟶⟨ 𝕊' ∣ M' ⟩`.
--
--
-- Where to look, under `OperationalSemantics/`
--   State             states, their grade and extensions (State,
--                     state-grade, _≤ₛ_)
--   Reduction         configurations and reduction (Config, _⟶_)
--   StateEquivalence  states up to the term equivalence

import MonomorphicCalculus.OperationalSemantics.Reduction
import MonomorphicCalculus.OperationalSemantics.State
import MonomorphicCalculus.OperationalSemantics.StateEquivalence
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Bisimulation
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Core
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Extensions
import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Replay

------------------------------------------------------------------------
-- Type safety                                                        --
------------------------------------------------------------------------

-- Type safety in terms of progress and preservation.
--
-- Where to look, under `OperationalSemantics/`
--   TypeSafety  progress and preservation

import MonomorphicCalculus.OperationalSemantics.TypeSafety

------------------------------------------------------------------------
-- Termination                                                        --
------------------------------------------------------------------------

-- Termination (strong normalisation) proven using logical relations.
--
-- Where to look, under `OperationalSemantics/`
--   Evaluation                runs that halt (Halts)
--   GradedReach               graded reachability
--   Termination               the theorem
--   Termination/Reducibility  the logical relation (VRed, CRed, SRed)

import MonomorphicCalculus.OperationalSemantics.Evaluation
import MonomorphicCalculus.OperationalSemantics.GradedReach
import MonomorphicCalculus.OperationalSemantics.Termination
import MonomorphicCalculus.OperationalSemantics.Termination.Bind
import MonomorphicCalculus.OperationalSemantics.Termination.Environment
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Action
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Cell
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Core
import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Variables
import MonomorphicCalculus.OperationalSemantics.Termination.Handle
import MonomorphicCalculus.OperationalSemantics.Termination.Reducibility

------------------------------------------------------------------------
-- Running operations by top-level (pure) implementations             --
------------------------------------------------------------------------

-- Model of a (pure)  top-level semantics that replaces an operation call
-- by the value of its implementation, with preservation and progress.
--
-- Where to look, under `OperationalSemantics/`
--   TopLevel            the machine (TopLevelOpSemantics)
--   TopLevel/Reduction  preservation
--   TopLevel/Progress   progress

import MonomorphicCalculus.OperationalSemantics.TopLevel
import MonomorphicCalculus.OperationalSemantics.TopLevel.Progress
import MonomorphicCalculus.OperationalSemantics.TopLevel.Reduction

------------------------------------------------------------------------
-- Equational theory                                                  --
------------------------------------------------------------------------

-- A local state theory based equational theory of values and computations.
--
-- Where to look
--   EquationalTheory/EquationalTheory  the theory (_⊢ᵛ⦂_≡ᵗʰ_, _⊢ᶜ⦂_≡ᵗʰ_)
--   EquationalTheory/Alignment         the term equivalence lies within it

import MonomorphicCalculus.EquationalTheory.Alignment
import MonomorphicCalculus.EquationalTheory.EquationalTheory
import MonomorphicCalculus.EquationalTheory.Naturality

------------------------------------------------------------------------
-- Models                                                             --
------------------------------------------------------------------------

-- A general model is a setoid-enriched cartesian closed category with the box
-- modality `[ ρ ]` and the context modality `⟨ ρ ⟩` in a graded adjunction.
--
-- Where to look, under `DenotationalSemantics/Model/`
--   Category                       the setoid-enriched cartesian closed
--                                  category
--   Modality/Future                the box modality `[ ρ ]`
--   Modality/Past                  the context modality `⟨ ρ ⟩`
--   Modality/Adjunction            their graded adjunction
--   Modality/Eternal               eternal objects (Eternalᵒ)
--   GroundTypes, GroundEternal     ground types
--   Comparison, ComparisonEternal  their comparisons, which commute with the
--                                  eternal extraction
--   Monad                          the strong graded monad with handler values
--   TickMonad, Implementation      the tick monad and implementations of the
--                                  operations, interpreting running operations
--                                  by implementations

import MonomorphicCalculus.DenotationalSemantics.Model.Category
import MonomorphicCalculus.DenotationalSemantics.Model.Comparison
import MonomorphicCalculus.DenotationalSemantics.Model.ComparisonEternal
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

------------------------------------------------------------------------
-- Interpretation                                                     --
------------------------------------------------------------------------

-- Types, contexts and terms are interpreted in any above model.
--
-- Where to look, under `DenotationalSemantics/Interpretation/`
--   Types                       types (⟦_⟧ᵛ, ⟦_⟧ᶜ)
--   Contexts                    contexts (⟦_⟧ᶜᵗˣ)
--   Terms                       terms (⟦_⟧ᵛᵗ, ⟦_⟧ᶜᵗ), with uniform handlers
--                               (Paramᵛ, Paramᶜ)
--   RenamingCoherence           naturality in renamings
--   SubstitutionCoherence/Core  naturality in substitutions

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

------------------------------------------------------------------------
-- Soundness                                                          --
------------------------------------------------------------------------

-- For terms with uniformly defined handlers, equal terms have equal
-- denotations, and a run relates the denotations of its configurations.
--
-- Where to look
--   EquationalTheory/Soundness  the equational theory
--   OperationalSemantics/Soundness/Preservation
--                               the reduction
--   OperationalSemantics/Soundness/TopLevel
--                               running operations by implementations

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
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Base
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Handle
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.HandleOpClause
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.HandleOpCont
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Step
import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Unbox
import MonomorphicCalculus.OperationalSemantics.Soundness.TickLemmas
import MonomorphicCalculus.OperationalSemantics.Soundness.TopLevel

------------------------------------------------------------------------
-- The presheaf model                                                 --
------------------------------------------------------------------------

-- Presheaves over a Kripke frame of worlds, with the free graded monad
-- on them, given an instance of the general notion of a model.
--
-- Where to look
--   DenotationalSemantics/Model/World  Kripke frames of worlds (World)
--   DenotationalSemantics/Model/Example/PSh/
--     Base                 presheaves (PShCat)
--     Monad/Instance       the free graded monad (PShMonad)
--     Monad/HandlerValues  handler values (Hᵖ, appʰᵖ, curryʰᵖ)

import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Implementation
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Eternal
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Effects
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.HandlerValues
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Laws
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Mu
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Instance
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.TickMonad
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.TopLevelInstance
import MonomorphicCalculus.DenotationalSemantics.Model.World
import MonomorphicCalculus.DenotationalSemantics.Model.World.Action
import MonomorphicCalculus.DenotationalSemantics.Model.World.History
import MonomorphicCalculus.DenotationalSemantics.Model.World.Product
import MonomorphicCalculus.DenotationalSemantics.Model.World.Reindex

------------------------------------------------------------------------
-- Adequacy                                                           --
------------------------------------------------------------------------

-- In a head-faithful model, two programs with uniform handlers and equal
-- denotations halt with the same outcome, e.g., in the presheaf model.
--
-- Where to look
--   Adequacy/HeadFaithful      head-faithful models (HeadFaithful)
--   Adequacy/Adequacy          adequacy
--   Adequacy/PSh/HeadFaithful  the presheaf model is head-faithful
--   Adequacy/Equational        the equational theory is observationally valid

import MonomorphicCalculus.Adequacy.Adequacy
import MonomorphicCalculus.Adequacy.Equational
import MonomorphicCalculus.Adequacy.HeadFaithful
import MonomorphicCalculus.Adequacy.PSh.HeadFaithful
import MonomorphicCalculus.Adequacy.PSh.TickFrames
import MonomorphicCalculus.Adequacy.PSh.TreeHead
import MonomorphicCalculus.Adequacy.PSh.TreeShape

------------------------------------------------------------------------
-- Examples                                                           --
------------------------------------------------------------------------

-- Concrete Kripke frames of worlds, typed computations, and the adjoints
-- of the context modality at particular grades.
--
-- Where to look
--   DenotationalSemantics/Model/Example/World
--                             Kripke frames
--   Examples/Typing           typed computations

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World
import MonomorphicCalculus.Examples.Typing
