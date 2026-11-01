------------------------------------------------------------------------
-- The polymorphic calculus and its type inference                    --
--                                                                    --
-- Every module of the polymorphic calculus and of its type           --
-- inference: syntax, hypotheses, typing and its structural           --
-- properties, operational semantics, type safety and termination,    --
-- programs, constraints and their solving, and principal type        --
-- schemes.                                                           --
--                                                                    --
-- The calculus is parameterised by a language spec. (`LanguageSpec`, --
-- in `Language/Spec`): a grade system, base types and an operation   --
-- signature; `withoutBaseTypes` is the instance without base types.  --
-- Inference also takes hints for the grade system (`SystemHints`, in --
-- `Grades/Hints`), read only by the solver, and an enumeration of    --
-- the operations (`OpEnum`, in `Inference/SolverImpl/Enum`).         --
--                                                                    --
-- Module paths below are relative to `PolymorphicCalculus/`.         --
--                                                                    --
-- Check with `agda PolymorphicCalculus/Everything.agda`.             --
--                                                                    --
-- The inference examples are checked with                            --
--   `agda PolymorphicCalculus/Examples.agda`.                        --
------------------------------------------------------------------------

module PolymorphicCalculus.Everything where

------------------------------------------------------------------------
-- Grade systems                                                      --
------------------------------------------------------------------------

-- Grade systems live in `Grades/` and are checked by the root
-- `Everything.agda`. A grade system is a grade algebra for effects, one
-- for resources, and a grade morphism between them. The examples include
-- grades of time over ℕ and ℚ≥0, operation counts, security levels,
-- regular expressions and timed traces, grade systems pairing two of
-- them, and pairs of grades with no grade morphism between them.
--
-- Where to look, under `Grades/`
--   Base       grade systems, grade algebras and grade morphisms
--              (GradeSystem, Grade, GradeMorphism)
--   Examples/  the example grades and grade systems

------------------------------------------------------------------------
-- Syntax                                                             --
------------------------------------------------------------------------

-- Scopes of type, resource-grade and effect-grade variables, open grade
-- expressions, types, contexts and terms. Raw terms are well scoped but
-- untyped; run-time terms are raw terms without grades and type annotations.
--
-- Where to look
--   Syntax/Scopes             scopes (Scope)
--   Syntax/Grades             open grade expressions (EExp, RExp)
--   Syntax/Types              value and computation types, among them the
--                             handler types `C ⇛ D` (OVType, OCType)
--   Syntax/Contexts           program contexts of schemes, and variable 
--                             contexts of terms (PCtx, Scheme, OCtx)
--   Syntax/GradeSubstitution  substitutions for type and grade variables
--   Syntax/Raw                raw values and computations, among them
--                             `handler H`, `handle M with V` and the uses
--                             `usedef k` of definitions (RawV, RawC)
--   Syntax/Run                run-time terms, and erasure to them (RunV,
--                             RunC, eraseᵛ, eraseᶜ)

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

------------------------------------------------------------------------
-- Hypotheses                                                         --
------------------------------------------------------------------------

-- Typing takes place under hypotheses: grade orderings, quantified
-- orderings, eternality, subtyping, and the disjunctions of var. rule.
--
-- Where to look
--   Hypotheses             hypotheses (Hyps), the disjunctions of the 
--                          variable rule (_⊩_Et∨≾ᵘ_), grade entailment
--                          (_⊩_≾̂ₑ_, _⊩_≾̂ᵣ_) and open subtyping (_⊩_<:̂ᵛ_)
--   Hypotheses/Quantified  quantified orderings (QOrd)
--   Hypotheses/Instances   closed instances `δ ⊨ Q` and satisfiability
--                          (Satisfiable)

import PolymorphicCalculus.Hypotheses
import PolymorphicCalculus.Hypotheses.Instances
import PolymorphicCalculus.Hypotheses.Quantified

------------------------------------------------------------------------
-- Type system                                                        --
------------------------------------------------------------------------

-- The judgements `Q ∣ Γ ⊢ᵛ V : X` and `Q ∣ Γ ⊢ᶜ M : C` as intrinsically
-- typed derivations, with the rules Var, UseDef, Box, Unbox, Handler, etc.
--
-- Where to look
--   Typing              the judgements (_∣_⊢ᵛ⦂_, _∣_⊢ᶜ⦂_) and resource access
--                       (_⊢_∈̂[_]_)
--   Typing/Erasure      erasure of derivations to raw terms (⌊_⌋ᵛ, ⌊_⌋ᶜ, ⌊_⌋ʳ)
--   Typing/Resources    values of box type
--   Typing/ScopeClosed  the scope-closed typing of a run-time term (_⊢ᵛ_⦂_,
--                       _⊢ᶜ_⦂_): a derivation over the empty scope and under
--                       no hypotheses that erases to it

import PolymorphicCalculus.Typing
import PolymorphicCalculus.Typing.Erasure
import PolymorphicCalculus.Typing.Resources
import PolymorphicCalculus.Typing.ScopeClosed

------------------------------------------------------------------------
-- Structural properties of typing                                    --
------------------------------------------------------------------------

-- Typing is stable under substitution of types and grades, renaming and
-- substitution of term variables, conversion of a context's types, and
-- instantiation of the scope.
--
-- Where to look
--   Typing/GradeSubstitution  substitution of types and grades
--   Typing/Renaming           renaming of term variables
--   Typing/Substitution       substitution of term variables
--   Typing/Inversion          inversion
--   Typing/Conversion         conversion of a context's types
--   Typing/Instantiation      instantiation of the scope
--   Typing/Transport          transport of derivations along equations

import PolymorphicCalculus.Typing.Conversion
import PolymorphicCalculus.Typing.GradeSubstitution
import PolymorphicCalculus.Typing.Instantiation
import PolymorphicCalculus.Typing.Inversion
import PolymorphicCalculus.Typing.Renaming
import PolymorphicCalculus.Typing.Substitution
import PolymorphicCalculus.Typing.Transport

------------------------------------------------------------------------
-- Operational semantics                                              --
------------------------------------------------------------------------

-- A small-step reduction rel. `⟨ 𝕊 ∣ M ⟩⟶⟨ 𝕊' ∣ M' ⟩` of run-time terms.
--
-- Where to look, under `OperationalSemantics/`
--   State      states and state typings, with their extensions (State,
--              StateTyping, _≤ₛ_, _⊆[_]_)
--   Reduction  the reduction (Step)

import PolymorphicCalculus.OperationalSemantics.Reduction
import PolymorphicCalculus.OperationalSemantics.State

------------------------------------------------------------------------
-- Type safety and termination                                        --
------------------------------------------------------------------------

-- Type safety and termination results.
--
-- Where to look, under `OperationalSemantics/`
--   TypeSafety                progress and preservation
--   Termination               termination
--   Termination/Reducibility  the reducibility relation (VRed, CRed)

import PolymorphicCalculus.OperationalSemantics.Termination
import PolymorphicCalculus.OperationalSemantics.Termination.Reducibility
import PolymorphicCalculus.OperationalSemantics.TypeSafety

------------------------------------------------------------------------
-- Programs                                                           --
------------------------------------------------------------------------

-- A program is a sequence of top-level (let) definitions `f = V`.
--
-- Where to look, under `Programs/`
--   Syntax         programs (Program), erased with the definitions
--                  substituted (⟦_⟧ᴾ, ⌊_⌋ᴾᶜ)
--   Typing         the program judgement (⊢ᴾ_⦂_)
--   Substitution   substitution of closed typings of the definitions
--                  for their uses (sdef-v, sdef-c)
--   Instantiation  instantiation

import PolymorphicCalculus.Programs.Instantiation
import PolymorphicCalculus.Programs.Substitution
import PolymorphicCalculus.Programs.Syntax
import PolymorphicCalculus.Programs.Typing

------------------------------------------------------------------------
-- Constraints                                                        --
------------------------------------------------------------------------

-- Constraints generated during type inference.
--
-- Where to look, under `Inference/`
--   Constraints/Syntax        constraints (Constraint)
--   Constraints/Satisfaction  their solutions (_⊨[_]_)
--   Constraints/Schemes       instances of schemes (instᶜ)
--   Generate                  generation (genV, genC)
--   Soundness                 soundness of generation
--   Completeness              completeness of generation

import PolymorphicCalculus.Inference.Completeness
import PolymorphicCalculus.Inference.Constraints.Properties
import PolymorphicCalculus.Inference.Constraints.Satisfaction
import PolymorphicCalculus.Inference.Constraints.Schemes
import PolymorphicCalculus.Inference.Constraints.Syntax
import PolymorphicCalculus.Inference.Generate
import PolymorphicCalculus.Inference.Soundness

------------------------------------------------------------------------
-- Solving                                                            --
------------------------------------------------------------------------

-- Interface of a principal solver, and a reference implementation of it.
--
-- Where to look, under `Inference/`
--   Solver      the interface of a principal solver (Solver)
--   SolverImpl  the solver (solver), and the modules for its parts below it

import PolymorphicCalculus.Inference.Outcome
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

------------------------------------------------------------------------
-- Principal type schemes and inference                               --
------------------------------------------------------------------------

-- A term is typable exactly when the hypotheses of its principal type
-- scheme are satisfiable. Inference returns a principal scheme, `untypable`,
-- or `stuck`, and is complete with respect to scope-closed typings.
--
-- Where to look
--   Inference/Principality  principal type schemes, of values in program
--                           contexts and of computations in open contexts
--                           (PrincipalSchemeᵛ, PrincipalScheme)
--   Inference/Values        inference for values in program contexts (inferᵛ)
--   Inference/SolverImpl    inference for computations in open contexts
--                           (infer)
--   Inference/ScopeClosed   completeness for computations
--   Programs/Checking       checking a program (checkProgram): each definition
--                           inferred in the program context of those before
--                           it, and its scheme added

import PolymorphicCalculus.Inference.Principality
import PolymorphicCalculus.Inference.ScopeClosed
import PolymorphicCalculus.Inference.Values
import PolymorphicCalculus.Programs.Checking
