------------------------------------------------------------------------------
-- Every module of the polymorphic calculus and its type inference part.    --
--                                                                          --
-- The comments below name the key modules, with their main definitions     --
-- and results; module paths are relative to `PolymorphicCalculus/`.        --
--                                                                          --
-- The calculus is parameterised by a `LanguageSpec` (`Language/Spec`): a   --
-- grade system, base types and an operation signature; `withoutBaseTypes`  --
-- is the instance without base types. Inference also takes `SystemHints`   --
-- for the grade system (`Grades/Hints`), read only by the solver, and an   --
-- `OpEnum` of the operations (`Inference/SolverImpl/Enum`).                --
--                                                                          --
-- Check with `agda PolymorphicCalculus/Everything.agda`; the inference     --
-- examples are checked apart, by `agda PolymorphicCalculus/Examples.agda`. --
------------------------------------------------------------------------------

module PolymorphicCalculus.Everything where

---- Grade systems are in `Grades/`, checked by the root `Everything.agda`. A
---- grade system (`GradeSystem`, in `Grades/Base`) is a grade algebra
---- (`Grade`) for effects, one for resources, and a grade morphism
---- (`GradeMorphism`) between them. `Grades/Examples/` holds grades of time
---- over ℕ and ℚ≥0, operation counts, security levels, regular expressions
---- and timed traces, grade systems pairing two of them, and absences of
---- grade morphisms (in `Grades/Examples/`: `no-projection`, in
---- `System/Counts/Time`; `erases` and `miscounts`, in
---- `System/Counts/Timed/RightSided`; `no-morphism`, in
---- `Traces/Regular/Subsets`).

---- Syntax: scopes of type, resource-grade and effect-grade variables
---- (`Scope`, in `Syntax/Scopes`); open grade expressions (`EExp`, `RExp`,
---- in `Syntax/Grades`); value and computation types (`OVType`, `OCType`,
---- in `Syntax/Types`), among them the handler types `C ⇛ D`; program
---- contexts `Δ` of closed type schemes `∀ Θ. Q ⇒ X` (`PCtx`, `Scheme`), a
---- definition named by its position, and contexts `Γ` starting with a
---- program context (`OCtx`, in `Syntax/Contexts`); substitutions; raw
---- (well-scoped, untyped) values and computations (`RawV`, `RawC`, in
---- `Syntax/Raw`), among them `handler H`, `handle M with V` and the uses
---- `usedef k` of definitions; and run-time terms, raw terms without grades
---- and type annotations (`RunV`, `RunC`, `eraseᵛ`, `eraseᶜ`, in
---- `Syntax/Run`).

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

---- Hypotheses (`Hyps`, in `Hypotheses`): grade orderings, quantified
---- orderings (`QOrd`, in `Hypotheses/Quantified`), eternality, subtyping
---- and the disjunctions of the variable rule (`VarOK`). Grade entailment
---- (`_⊩_≾̂ₑ_`, `_⊩_≾̂ᵣ_`) is semantic consequence: an ordering holding at
---- every closed instance satisfying the grade hypotheses. It is closed
---- under the laws of the grade algebras, contains every true ordering
---- (`factₑ`, rule Truth), instantiates a quantified hypothesis at any
---- instance of its rigids (`instₑ`, rule Inst), and is stable under
---- substitution (`⊩-substₑ`, `⊩-substᵣ`); a quantified ordering is
---- entailed exactly when it is a semantic consequence (`⊩ᴼ⇒⊨ᴼ`, `⊨ᴼ⇒⊩ᴼ`).
---- Open subtyping (`_∣_<:̂ᵛ_`) is a preorder reflecting eternality. Closed
---- instances `δ ⊨ Q` and `Satisfiable` are in `Hypotheses/Instances`,
---- where entailment is sound at a satisfying closed instance
---- (`sound-≾ₑ⁰`, `sound-≾ᵣ⁰`, `⊨⇒⊩ᴴ`).

import PolymorphicCalculus.Hypotheses
import PolymorphicCalculus.Hypotheses.Instances
import PolymorphicCalculus.Hypotheses.Quantified

---- Type system: the judgements `Q ∣ Γ ⊢ V : X` and `Q ∣ Γ ⊢ M : C` as
---- intrinsically typed derivations (`_∣_⊢V⦂_`, `_∣_⊢C⦂_`, in `Typing`),
---- with the rules Var, UseDef, Box, Unbox, Handler, Handle and the rest;
---- Unbox takes a resource value, a variable under annotations
---- (`_∣_⊢↪[_]_⦂[_]_`). A typing of a raw term is a derivation erasing to
---- it (`⌊_⌋ᵛ`, `⌊_⌋ᶜ`, `⌊_⌋ʳ`, in `Typing/Erasure`). Under a program
---- context whose schemes have non-resource types, a value of box type is
---- a resource value (`resource-value`, in `Typing/Resources`). The
---- scope-closed typing of a run-time term (`_⊢ᵛ_⦂_`, `_⊢ᶜ_⦂_`, in
---- `Typing/ScopeClosed`) is a derivation over the empty scope and under no
---- hypotheses erasing to it.

import PolymorphicCalculus.Typing
import PolymorphicCalculus.Typing.Erasure
import PolymorphicCalculus.Typing.Resources
import PolymorphicCalculus.Typing.ScopeClosed

---- Structural properties of typing: substitution of types and grades
---- (`substᵛ`, `substᶜ`, in `Typing/GradeSubstitution`), renaming
---- (`rename-v`, `rename-c`) and, under no hypotheses, substitution
---- (`sub-v`, `sub-c`) of term variables, inversion (`invV`, `invC`),
---- conversion of a context's types (`conv-v`, `conv-c`, in
---- `Typing/Conversion`: to equivalent types under any hypotheses, to
---- subtypes under hypotheses with no disjunction), and instantiation of
---- the scope alone (`scope-instantiation`, in `Typing/Instantiation`).

import PolymorphicCalculus.Typing.Conversion
import PolymorphicCalculus.Typing.GradeSubstitution
import PolymorphicCalculus.Typing.Instantiation
import PolymorphicCalculus.Typing.Inversion
import PolymorphicCalculus.Typing.Renaming
import PolymorphicCalculus.Typing.Substitution
import PolymorphicCalculus.Typing.Transport

---- Operational semantics, on run-time terms: states and state typings,
---- with their extensions (`State`, `StateTyping`, `_≤ₛ_`, `_⊆[_]_`, in
---- `OperationalSemantics/State`), and the reduction
---- `⟨ S ∣ M ⟩↝⟨ S' ∣ M' ⟩` (`Step`, in `OperationalSemantics/Reduction`).
---- HANDLE-OP leaves the clause's grade variable uninstantiated; CMP
---- decides a comparison by the structural order on the data its operands
---- denote (`compareᴰ`).

import PolymorphicCalculus.OperationalSemantics.Reduction
import PolymorphicCalculus.OperationalSemantics.State

---- Type safety (`type-safety`, in `OperationalSemantics/TypeSafety`): a
---- run-time term with a scope-closed typing over a typed state is finished
---- (`Final`) or steps; an extension of the state typing types the new
---- state and the new term at a subtype, its grade after the step's
---- below the original (`progress`, `preservation`). Termination
---- (`termination`, in `OperationalSemantics/Termination`): a run-time term
---- typed in the empty context halts from the empty state (`Halts`), by the
---- fundamental lemma (`fund-v`, `fund-c`) of the reducibility relation
---- (`VRed`, `CRed`, in `OperationalSemantics/Termination/Reducibility`).

import PolymorphicCalculus.OperationalSemantics.Termination
import PolymorphicCalculus.OperationalSemantics.Termination.Reducibility
import PolymorphicCalculus.OperationalSemantics.TypeSafety

---- Programs: sequences of definitions `f = V` (`Program`, in
---- `Programs/Syntax`), erased with the definitions substituted (`⟦_⟧ᴾ`,
---- `⌊_⌋ᴾᶜ`); the program judgement (`⊢ᴾ_⦂_`, in `Programs/Typing`), each
---- definition typable in the program context of those before it and bound
---- to its principal type scheme there; the substitution of closed typings
---- of the definitions for their uses (`sdef-v`, `sdef-c`, in
---- `Programs/Substitution`). Instantiation (`instantiation`,
---- `instantiationᵛ`, in `Programs/Instantiation`): in a typed program, at
---- every closed instance `δ ⊨ Q`, a typing under `Q` gives a scope-closed
---- typing of the erasure of the instantiated term, handler clauses staying
---- typed at their grade variables. By it, a term typed in the program
---- context of a typed program is typed in the empty state at every closed
---- instance, and halts (`programs`).

import PolymorphicCalculus.Programs.Instantiation
import PolymorphicCalculus.Programs.Substitution
import PolymorphicCalculus.Programs.Syntax
import PolymorphicCalculus.Programs.Typing

---- Constraints (`Constraint`, in `Inference/Constraints/Syntax`), their
---- solutions (`_⊨[_]_`, in `Inference/Constraints/Satisfaction`) and their
---- generation (`genV`, `genC`, in `Inference/Generate`). Generation is
---- sound (`soundV`, `soundC`, in `Inference/Soundness`) and complete
---- (`completeV`, `completeC`, in `Inference/Completeness`): the solutions
---- of the constraint generated from a term are its typings (`charV`,
---- `charC`). A use of a definition generates an instance of its scheme,
---- its hypotheses as a constraint (`instᶜ`, in
---- `Inference/Constraints/Schemes`).

import PolymorphicCalculus.Inference.Completeness
import PolymorphicCalculus.Inference.Constraints.Properties
import PolymorphicCalculus.Inference.Constraints.Satisfaction
import PolymorphicCalculus.Inference.Constraints.Schemes
import PolymorphicCalculus.Inference.Constraints.Syntax
import PolymorphicCalculus.Inference.Generate
import PolymorphicCalculus.Inference.Soundness

---- Solving: the interface of a principal solver (`Solver`, in
---- `Inference/Solver`), and the solver meeting it (`solver`, in
---- `Inference/SolverImpl`), not stuck on constraints without `∀`
---- (`runSolver-rigidFree`).

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

---- Principal type schemes (`PrincipalSchemeᵛ`, `PrincipalScheme`, in
---- `Inference/Principality`), of values in program contexts and of
---- computations in open contexts: a term is typable exactly when the
---- hypotheses of its scheme are satisfiable (`typableᵛ-⇔`, `typable-⇔`).
---- Type inference for values in program contexts (`inferᵛ`, in
---- `Inference/Values`): a scheme it answers is principal (`inferᵛ-typed`);
---- it answers `untypable` only for untypable values (`inferᵛ-untypable`),
---- and `stuck` only for values with handlers or using a definition whose
---- scheme has quantified hypotheses (`inferᵛ-noRigid`); the same for
---- computations in open contexts (`infer`, `infer-typed`,
---- `infer-untypable`, `infer-noRigid`, in `Inference/SolverImpl`).
---- Completeness (`completenessᵛ`, in `Inference/Values`; `completeness`,
---- in `Inference/ScopeClosed`): inference refutes no scope-closed typing,
---- of a value in any program context or of a computation in a context over
---- the empty scope, and every scheme it answers has a closed instance with
---- its type below the typing's. Checking a program (`checkProgram`, in
---- `Programs/Checking`) infers each definition in the program context of
---- those before it and adds its scheme.

import PolymorphicCalculus.Inference.Principality
import PolymorphicCalculus.Inference.ScopeClosed
import PolymorphicCalculus.Inference.Values
import PolymorphicCalculus.Programs.Checking
