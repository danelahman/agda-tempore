------------------------------------------------------------------------
-- The monomorphic calculus                                           --
--                                                                    --
-- Every module of the monomorphic calculus: its syntax, operational  --
-- semantics and type safety, termination, equational theory,         --
-- denotational semantics with soundness and adequacy, and examples.  --
--                                                                    --
-- The calculus is parameterised by a language (`LanguageSpec`, in    --
-- `Language/Spec`): a grade system, base types and an operation      --
-- signature. Module paths below are relative to                      --
-- `MonomorphicCalculus/`.                                            --
--                                                                    --
-- Check with `agda MonomorphicCalculus/Everything.agda`.             --
------------------------------------------------------------------------

module MonomorphicCalculus.Everything where

------------------------------------------------------------------------
-- Syntax                                                             --
------------------------------------------------------------------------

-- Types, contexts and terms. A context lists variables and modalities
-- `⟨ ρ ⟩`. The variable rule asks that a variable's type be eternal, or
-- that the grade of the modalities after it lie below the unit. Values
-- and computations are intrinsically typed.
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
--
-- Main results
--   <:ᵛ-refl, <:ᵛ-trans  subtyping is a preorder
--   <:ᵛ-antisym          it is antisymmetric where the grade orders are
--   <:ᵛ-eternalˡ         a subtype of an eternal type is eternal
--   eternal-val-ext      a value of eternal type stays typed under a modality
--   grad-typ⇒var<:       a value of box type is a variable of a box subtype

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

-- Renamings are built from weakening, exchange, variables and the
-- renamings of modalities, and act on terms; at the generators the
-- action gives the structural rules. Substitution is defined over
-- parallel substitutions. On renamings, the context modality `_⟨ ρ ⟩`
-- has a left adjoint only at the unit, and is a parametric right adjoint
-- at every grade when the unit is the greatest grade.
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
--   Syntax/Renaming/ContextModality  the adjoints of the context modality
--   Syntax/Renaming/ContextModality/LowerBounds
--                                    parametric right adjoints
--   Syntax/Renaming/ContextModality/Adjunction
--                                    their hom-set forms
--
-- Main results
--   unbox-val          unboxing any value of box type is derivable
--   C-normal-form      a computation has a derivation with the same erasure
--                      whose subsumptions sit only at the reconciliation
--                      points
--   left-adjoint⇔unit  the context modality has a left adjoint exactly at the
--                      unit
--   PRA-everywhere     it is a parametric right adjoint at every grade when
--                      the unit is the greatest grade
--   PRA⇒no-factor      where it is one, `σ · σ' ≾ ρ` with `σ' ≾ ρ` forces
--                      `σ ≾ 𝟏`
--   left-adjoint⇔hom   a left adjoint amounts to a natural bijection
--                      `Ren [] E Δ ≅ Ren [] Γ (Δ ⟨ ρ ⟩)`
--   PRA⇔hom            a parametric right adjoint amounts to a natural
--                      bijection onto the renamings over each
--                      `s : Ren [] Γ ([] ⟨ ρ ⟩)`

import MonomorphicCalculus.Syntax.Normalisation
import MonomorphicCalculus.Syntax.Renaming
import MonomorphicCalculus.Syntax.Renaming.Action
import MonomorphicCalculus.Syntax.Renaming.Base
import MonomorphicCalculus.Syntax.Renaming.Category
import MonomorphicCalculus.Syntax.Renaming.Coherence
import MonomorphicCalculus.Syntax.Renaming.Equivalence
import MonomorphicCalculus.Syntax.Renaming.ContextModality
import MonomorphicCalculus.Syntax.Renaming.ContextModality.Adjunction
import MonomorphicCalculus.Syntax.Renaming.ContextModality.LowerBounds
import MonomorphicCalculus.Syntax.Renaming.ContextModality.Model
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

-- A small-step reduction of configurations, each a computation over a
-- state. A comparison is a value, and CMP decides it to its boolean
-- constant where `if` scrutinises it. SUB and the SUB-… rules move a
-- subsumption and erase to the identity on raw terms; HANDLE-RET,
-- HANDLE-OP and HANDLE-STEP fire on a handler literal.
--
-- Where to look, under `OperationalSemantics/`
--   State             states, their grade and extensions (State, state-grade,
--                     _≤ₛ_)
--   Reduction         configurations and reduction (Config, _⟶_)
--   StateEquivalence  states up to the term equivalence
--
-- Main results
--   final-no-step  a returned value or an operation call is finished (Final)
--                  and makes no step

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

-- A typed computation over a state is finished or takes a step, and the
-- step keeps it typed.
--
-- Where to look, under `OperationalSemantics/`
--   TypeSafety  progress and preservation
--
-- Main results
--   progress            a computation over a state is finished (Final) or
--                       steps (Steps)
--   step-extends-state  a step extends the state
--   preservation        the computation a step reaches is typed at a subtype,
--                       its grade after the step's below the original
--   type-safety         progress and preservation together

import MonomorphicCalculus.OperationalSemantics.TypeSafety

------------------------------------------------------------------------
-- Termination                                                        --
------------------------------------------------------------------------

-- A program run from the empty state halts, with a returned value or an
-- operation call. The proof is the fundamental lemma of a logical
-- relation indexed by graded reachability.
--
-- Where to look, under `OperationalSemantics/`
--   Evaluation                runs that halt (Halts)
--   GradedReach               graded reachability
--   Termination               the theorem
--   Termination/Reducibility  the logical relation (VRed, CRed, SRed)
--
-- Main results
--   termination  a program run from the empty state halts (in Termination)

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
-- Running operations by implementations                              --
------------------------------------------------------------------------

-- A machine that replaces an operation call by the value of its
-- implementation, with preservation and progress.
--
-- Where to look, under `OperationalSemantics/`
--   TopLevel            the machine (TopLevelOpSemantics)
--   TopLevel/Reduction  preservation
--   TopLevel/Progress   progress
--
-- Main results
--   PureTopLevelPreservationTheorem  preservation
--   PureTopLevelProgressTheorem      progress

import MonomorphicCalculus.OperationalSemantics.TopLevel
import MonomorphicCalculus.OperationalSemantics.TopLevel.Progress
import MonomorphicCalculus.OperationalSemantics.TopLevel.Reduction

------------------------------------------------------------------------
-- Equational theory                                                  --
------------------------------------------------------------------------

-- An equational theory of values and computations. The term equivalence
-- is contained in it.
--
-- Where to look
--   EquationalTheory/EquationalTheory  the theory (_⊢ᵛ⦂_≡ᵗʰ_, _⊢ᶜ⦂_≡ᵗʰ_)
--   EquationalTheory/Alignment         the term equivalence lies within it
--
-- Axioms
--   seq-return, seq-perform, seq-assoc, …  sequencing
--   fun-beta, fun-eta                      functions
--   handle-return, handle-perform, …       handling
--   delay-zero, delay-delay                delays
--   unbox-beta, box-comm, …                boxes

import MonomorphicCalculus.EquationalTheory.Alignment
import MonomorphicCalculus.EquationalTheory.EquationalTheory
import MonomorphicCalculus.EquationalTheory.Naturality

------------------------------------------------------------------------
-- Models                                                             --
------------------------------------------------------------------------

-- A model is a setoid-enriched cartesian closed category with the box
-- modality `[ ρ ]` and the context modality `⟨ ρ ⟩` in a graded
-- adjunction, eternal objects, ground types with their comparisons, and
-- a strong graded monad with handler values.
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
--
-- Handler values, in Monad
--   Hᵒ                  the object of handlers
--   appʰ                application at a handled grade below the declared one
--   curryʰ              abstraction of a natural family
--   curryʰ-β, curryʰ-η  its β and η laws

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

-- Types, contexts and terms are interpreted in any model, for
-- derivations whose handlers are uniform. The interpretation is natural
-- in renamings and in substitutions.
--
-- Where to look, under `DenotationalSemantics/Interpretation/`
--   Types                       types (⟦_⟧ᵛ, ⟦_⟧ᶜ)
--   Contexts                    contexts (⟦_⟧ᶜᵗˣ)
--   Terms                       terms (⟦_⟧ᵛᵗ, ⟦_⟧ᶜᵗ), with uniform handlers
--                               (Paramᵛ, Paramᶜ)
--   RenamingCoherence           naturality in renamings
--   SubstitutionCoherence/Core  naturality in substitutions
--
-- Main results
--   handle-in-β                 handling with a handler written in place
--                               denotes the fold of the clauses after the
--                               return clause
--   V-rename-nat, C-rename-nat  the interpretation is natural in renamings
--   V-subst-nat, C-subst-nat    and in substitutions

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

-- For terms with uniform handlers, equal terms have equal denotations,
-- and a run relates the denotations of its configurations.
--
-- Where to look
--   EquationalTheory/Soundness  the equational theory
--   OperationalSemantics/Soundness/Preservation
--                               the reduction
--   OperationalSemantics/Soundness/TopLevel
--                               running operations by implementations
--
-- Main results
--   soundᵛ, soundᶜ  equal terms with uniform handlers have equal denotations
--   ⟶*-⊳            a run with uniform handlers relates the denotations of its
--                   configurations, by a time transition and an
--                   effect-refining coercion
--   ⟶*ᵗ-sound       the same for running operations by implementations, into
--                   the tick monad

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
-- on them. Its handler values are families of Kripke functions over the
-- handled grades, natural along sub-effecting.
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
-- denotations halt with the same outcome. The presheaf model is
-- head-faithful. With soundness, derivations of the equational theory
-- between programs are observationally valid.
--
-- Where to look
--   Adequacy/HeadFaithful      head-faithful models (HeadFaithful)
--   Adequacy/Adequacy          adequacy
--   Adequacy/PSh/HeadFaithful  the presheaf model is head-faithful
--   Adequacy/Equational        the equational theory is observationally valid
--
-- Main results
--   adequacy                      programs with equal denotations halt with
--                                 the same outcome (Same-outcome)
--   adequacy-base, adequacy-bool  at an answer type, with the same answer
--   PShHeadFaithful               the presheaf model is head-faithful

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
--   Examples/ContextModality  the adjoints of the context modality at
--                             particular grades

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World
import MonomorphicCalculus.Examples.ContextModality
import MonomorphicCalculus.Examples.Typing
