------------------------------------------------------------------------
-- The polymorphic calculus and its type inference                    --
--                                                                    --
-- Every module of the polymorphic calculus and of its type           --
-- inference: syntax, hypotheses, typing and its structural           --
-- properties, operational semantics, type safety and termination,    --
-- programs, constraints and their solving, and principal type        --
-- schemes.                                                           --
--                                                                    --
-- The calculus is parameterised by a language (`LanguageSpec`, in    --
-- `Language/Spec`): a grade system, base types and an operation      --
-- signature; `withoutBaseTypes` is the instance without base types.  --
-- Inference also takes hints for the grade system (`SystemHints`, in --
-- `Grades/Hints`), read only by the solver, and an enumeration of    --
-- the operations (`OpEnum`, in `Inference/SolverImpl/Enum`). Module  --
-- paths below are relative to `PolymorphicCalculus/`.                --
--                                                                    --
-- Check with `agda PolymorphicCalculus/Everything.agda`. The         --
-- inference examples are checked apart, with                         --
-- `agda PolymorphicCalculus/Examples.agda`.                          --
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
--   Base       grade systems, grade algebras and grade morphisms (GradeSystem,
--              Grade, GradeMorphism)
--   Examples/  the example grades and grade systems
--
-- Missing grade morphisms, under `Grades/Examples/`
--   no-projection      no projection onto a grade that counts time (in
--                      System/Counts/Time)
--   erases, miscounts  every morphism into at-most counts forgets the
--                      operation, so its quota does not cover the run (in
--                      System/Counts/Timed/RightSided)
--   no-morphism        an embedding of trace grades that is not a grade
--                      morphism (in Traces/Regular/Subsets)

------------------------------------------------------------------------
-- Syntax                                                             --
------------------------------------------------------------------------

-- Scopes of type, resource-grade and effect-grade variables, open grade
-- expressions, types, contexts and terms. A program context `Δ` lists the
-- closed type schemes `∀ Θ. Q ⇒ X` of the definitions, each named by its
-- position; a context `Γ` starts with a program context. Raw terms are well
-- scoped but untyped; run-time terms are raw terms without grades and
-- type annotations.
--
-- Where to look
--   Syntax/Scopes             scopes (Scope)
--   Syntax/Grades             open grade expressions (EExp, RExp)
--   Syntax/Types              value and computation types, among them the
--                             handler types `C ⇛ D` (OVType, OCType)
--   Syntax/Contexts           program contexts of schemes, and contexts (PCtx,
--                             Scheme, OCtx)
--   Syntax/GradeSubstitution  substitutions for type and grade variables
--   Syntax/Raw                raw values and computations, among them
--                             `handler H`, `handle M with V` and the uses
--                             `usedef k` of definitions (RawV, RawC)
--   Syntax/Run                run-time terms, and erasure to them (RunV, RunC,
--                             eraseᵛ, eraseᶜ)

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
-- orderings, eternality, subtyping, and the disjunctions of the variable
-- rule. Grade entailment is semantic consequence: an ordering is
-- entailed when it holds at every closed instance satisfying the grade
-- hypotheses. It is closed under the laws of the grade algebras. Open
-- subtyping is a preorder reflecting eternality.
--
-- Where to look
--   Hypotheses             hypotheses (Hyps), the disjunctions of the variable
--                          rule (_⊩_Et∨≾ᵘ_), grade entailment (_⊩_≾̂ₑ_,
--                          _⊩_≾̂ᵣ_) and open subtyping (_⊩_<:̂ᵛ_)
--   Hypotheses/Quantified  quantified orderings (QOrd)
--   Hypotheses/Instances   closed instances `δ ⊨ Q` and satisfiability
--                          (Satisfiable)
--
-- Main results
--   factₑ                       entailment contains every true ordering (rule
--                               Truth)
--   instₑ                       it instantiates a quantified hypothesis at any
--                               instance of its rigids (rule Inst)
--   ⊩-substₑ, ⊩-substᵣ          it is stable under substitution
--   ⊩ᴼ⇒⊨ᴼ, ⊨ᴼ⇒⊩ᴼ                a quantified ordering is entailed exactly when
--                               it is a semantic consequence
--   sound-≾ₑ⁰, sound-≾ᵣ⁰, ⊨⇒⊩ᴴ  entailment is sound at a satisfying closed
--                               instance (in Hypotheses/Instances)

import PolymorphicCalculus.Hypotheses
import PolymorphicCalculus.Hypotheses.Instances
import PolymorphicCalculus.Hypotheses.Quantified

------------------------------------------------------------------------
-- Type system                                                        --
------------------------------------------------------------------------

-- The judgements `Q ∣ Γ ⊢ᵛ V : X` and `Q ∣ Γ ⊢ᶜ M : C` as intrinsically
-- typed derivations, with the rules Var, UseDef, Box, Unbox, Handler,
-- Handle and the rest. Unbox takes a resource value, a variable under
-- annotations, through the resource access `Q ⊢ [ ρ ] X ∈̂[ ρ' ] Γ`, with
-- rules Res-Var and Res-Ann. A typing of a raw term is a derivation that
-- erases to it.
--
-- Where to look
--   Typing              the judgements (_∣_⊢ᵛ⦂_, _∣_⊢ᶜ⦂_) and resource access
--                       (_⊢_∈̂[_]_)
--   Typing/Erasure      erasure of derivations to raw terms (⌊_⌋ᵛ, ⌊_⌋ᶜ, ⌊_⌋ʳ)
--   Typing/Resources    values of box type
--   Typing/ScopeClosed  the scope-closed typing of a run-time term (_⊢ᵛ_⦂_,
--                       _⊢ᶜ_⦂_): a derivation over the empty scope and under
--                       no hypotheses that erases to it
--
-- Main results
--   resource-value  under a program context whose schemes have non-resource
--                   types, a value of box type is a resource value

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
--
-- Main results
--   substᵛ, substᶜ       substitution of types and grades
--   rename-v, rename-c   renaming of term variables
--   sub-v, sub-c         substitution of term variables, under no hypotheses
--   invV, invC           inversion
--   conv-v, conv-c       conversion of a context's types: to equivalent types
--                        under any hypotheses, to subtypes under hypotheses
--                        with no disjunction
--   scope-instantiation  instantiation of the scope alone

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

-- A reduction `⟨ 𝕊 ∣ M ⟩⟶⟨ 𝕊' ∣ M' ⟩` of run-time terms over states.
-- HANDLE-OP leaves the clause's grade variable uninstantiated; CMP
-- decides a comparison by the structural order on the data its operands
-- denote (compareᴰ).
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

-- A run-time term with a scope-closed typing over a typed state is
-- finished or takes a step that keeps it typed. A run-time term typed in
-- the empty context halts from the empty state; the proof is the
-- fundamental lemma of a reducibility relation.
--
-- Where to look, under `OperationalSemantics/`
--   TypeSafety                progress and preservation
--   Termination               termination
--   Termination/Reducibility  the reducibility relation (VRed, CRed)
--
-- Main results
--   type-safety             a run-time term with a scope-closed typing over a
--                           typed state is finished (Final) or steps
--   progress, preservation  an extension of the state typing types the new
--                           state, and the new term at a subtype, its grade
--                           after the step's below the original
--   termination             a run-time term typed in the empty context halts
--                           from the empty state (Halts)
--   fund-v, fund-c          the fundamental lemma

import PolymorphicCalculus.OperationalSemantics.Termination
import PolymorphicCalculus.OperationalSemantics.Termination.Reducibility
import PolymorphicCalculus.OperationalSemantics.TypeSafety

------------------------------------------------------------------------
-- Programs                                                           --
------------------------------------------------------------------------

-- A program is a sequence of definitions `f = V`. The program judgement
-- types each definition in the program context of those before it and
-- binds it to its principal type scheme there. Instantiation turns a
-- typing in a typed program into a scope-closed typing of the erased
-- term, at every closed instance.
--
-- Where to look, under `Programs/`
--   Syntax         programs (Program), erased with the definitions substituted
--                  (⟦_⟧ᴾ, ⌊_⌋ᴾᶜ)
--   Typing         the program judgement (⊢ᴾ_⦂_)
--   Substitution   substitution of closed typings of the definitions for their
--                  uses (sdef-v, sdef-c)
--   Instantiation  instantiation
--
-- Main results
--   instantiation, instantiationᵛ  in a typed program, at every closed
--                                  instance `δ ⊨ Q`, a typing under `Q` gives
--                                  a scope-closed typing of the erasure of the
--                                  instantiated term, handler clauses staying
--                                  typed at their grade variables
--   programs                       a term typed in the program context of a
--                                  typed program is typed in the empty state
--                                  at every closed instance, and halts

import PolymorphicCalculus.Programs.Instantiation
import PolymorphicCalculus.Programs.Substitution
import PolymorphicCalculus.Programs.Syntax
import PolymorphicCalculus.Programs.Typing

------------------------------------------------------------------------
-- Constraints                                                        --
------------------------------------------------------------------------

-- Inference generates a constraint from a term; the solutions of that
-- constraint are exactly the term's typings. A use of a definition
-- generates an instance of its scheme, with the scheme's hypotheses as a
-- constraint.
--
-- Where to look, under `Inference/`
--   Constraints/Syntax        constraints (Constraint)
--   Constraints/Satisfaction  their solutions (_⊨[_]_)
--   Constraints/Schemes       instances of schemes (instᶜ)
--   Generate                  generation (genV, genC)
--   Soundness                 soundness of generation
--   Completeness              completeness of generation
--
-- Main results
--   soundV, soundC        generation is sound
--   completeV, completeC  and complete
--   charV, charC          the solutions of the constraint generated from a
--                         term are its typings

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

-- A principal solver, and the solver that meets its interface.
--
-- Where to look, under `Inference/`
--   Solver      the interface of a principal solver (Solver)
--   SolverImpl  the solver (solver), and the modules for its parts below it
--
-- Main results
--   runSolver-rigidFree  the solver is not stuck on constraints without `∀`

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
-- scheme are satisfiable. Inference answers a principal scheme,
-- `untypable`, or `stuck`, and is complete with respect to scope-closed
-- typings. A program is checked definition by definition.
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
--
-- Main results
--   typableᵛ-⇔, typable-⇔              a term is typable exactly when the
--                                      hypotheses of its scheme are
--                                      satisfiable
--   inferᵛ-typed, infer-typed          a scheme inference answers is principal
--   inferᵛ-untypable, infer-untypable  it answers `untypable` only for
--                                      untypable terms
--   inferᵛ-noRigid, infer-noRigid      it answers `stuck` only for terms with
--                                      handlers or using a definition whose
--                                      scheme has quantified hypotheses
--   completenessᵛ, completeness        inference refutes no scope-closed
--                                      typing, of a value in any program
--                                      context or of a computation in a
--                                      context over the empty scope, and every
--                                      scheme it answers has a closed instance
--                                      with its type below the typing's

import PolymorphicCalculus.Inference.Principality
import PolymorphicCalculus.Inference.ScopeClosed
import PolymorphicCalculus.Inference.Values
import PolymorphicCalculus.Programs.Checking
