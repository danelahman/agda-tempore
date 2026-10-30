------------------------------------------------------------------------
-- Overview of the polymorphic calculus
--
-- One entry per main definition, rule, lemma and theorem, under its
-- title: grade systems, the type system, the operational semantics,
-- instantiation and type safety, and type inference. Check it with
-- `agda Results.agda`; `Everything.agda` checks every module.
--
-- The calculus is parameterised by a `LanguageSpec` (a grade system, base
-- types and an operation signature); `withoutBaseTypes` is the instance
-- without base types. Inference also takes `SystemHints` for the grade
-- system, read only by the solver, and an `OpEnum` of the operations.
------------------------------------------------------------------------

module Results where

-- The language: a grade system, base types and an operation signature
open import Language.Spec public using (LanguageSpec; withoutBaseTypes)
open import Grades.Hints using (SystemHints)
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)


------------------------------------------------------------------------
-- Grade systems

module GradeSystems where

  -- Definition (Grades and grade systems)
  open import Grades.Durations public using (Duration)
  open import Grades.Durations.Nat public using (ℕᴰ)
  open import Grades.Durations.NonNegativeRational public using (ℚ≥0ᴰ)
  open import Grades.Base public
    using (GradeSystem; Plus)
    renaming (Grade to GradeAlgebra; GradeMorphism to GradeAlgebraMorphism)

  -- The solver's hints for a grade algebra and a grade system
  open import Grades.Hints public using (GradeHints; SystemHints)

  -- The grade algebras of time, counts and lattices
  open import Grades.Examples.Time.LeftSided public
    using () renaming (left-sided-intervals to lower-bounds)
  open import Grades.Examples.Time.RightSided public
    using () renaming (right-sided-intervals to upper-bounds)
  open import Grades.Examples.Time.TwoSidedWithInfinity public
    using () renaming (two-sided-intervals-with-∞ to intervals)
  open import Grades.Examples.Time.Dense.LeftSidedCut public
    using () renaming (dense-left-sided-cut-intervals to dense-lower-bounds)
  open import Grades.Examples.Time.Dense.RightSidedCut public
    using () renaming (dense-right-sided-cut-intervals to dense-upper-bounds)
  open import Grades.Examples.Time.Dense.TwoSided public
    using () renaming (dense-two-sided-intervals-with-∞ to dense-intervals)
  open import Grades.Examples.Counts.AtMost public
    using () renaming (at-most-counts to counts)
  open import Grades.Examples.SecurityLevel public
    using (LevelLattice) renaming (level-grade to lattice)
  open import Grades.Product public using () renaming (_×ᵍ_ to _×_)

  -- The regular expression grade algebras
  open import Grades.Exact.Base public using (Word)
  open import Grades.Exact.Order public using () renaming (_⊑_ to _fits_)
  open import Grades.Exact.Lift public using () renaming (_≾_ to _≾-Hoare_)
  open import Grades.Exact.Expression public using (Expr)
  open import Grades.Examples.Traces.Rigid.Rational.LeftSided public
    using () renaming (left-sided to regular-lower-bounds)
  open import Grades.Examples.Traces.Rigid.Rational.RightSided public
    using () renaming (right-sided to regular-upper-bounds)
  open import Grades.Examples.Traces.Rigid.Rational.TwoSided public
    using () renaming (two-sided to regular-intervals)


------------------------------------------------------------------------
-- Syntax

module Syntax (S : LanguageSpec) where

  -- Scopes and grade expressions
  open import PolymorphicCalculus.Syntax.Scopes public using (Scope; TyVar; RVar; EVar)
  open import PolymorphicCalculus.Syntax.Grades S public
    using () renaming (EExp to EffectGradeExpr; RExp to ResourceGradeExpr)

  -- Ground types: unit, booleans, natural numbers, the empty type,
  -- products, sums, lists, graded modal types and base types
  open import Language.GroundTypes (LanguageSpec.Grades S) (LanguageSpec.BTs S) public
    using () renaming (GType to GroundType)

  -- Value and computation types, among them the handler types `C ⇛ D`
  open import PolymorphicCalculus.Syntax.Types S public
    using (_⇛_) renaming (OVType to ValueType; OCType to ComputationType)

  -- Program contexts `Δ` of closed type schemes `∀ Θ. Q ⇒ X`, a
  -- definition named by its position; contexts, starting with a
  -- program context (`[]` the empty one, `Δ ▶ s` a nonempty one), and
  -- the lookup `x : X ∈_ρ Γ`
  open import PolymorphicCalculus.Syntax.Contexts S public
    using (Scheme; ∀ˢ; _∈ᵖ[_]_; ⌜_⌝ᵖ; defs; _∈̂[_]_)
    renaming (PCtx to ProgramContext; OCtx to Context)

  -- Typing hypotheses, among them quantified orderings. Definition
  -- (Entailment): grade orderings, semantic consequence in the grade
  -- system, an ordering entailed when it holds by value at every closed
  -- instance satisfying the grade part of the hypotheses; a quantified
  -- ordering, entailed at fresh rigids (rule Gen); eternality,
  -- subtyping, the disjunction of the variable rule, and `Q ⊩ Q'[δ]`
  -- and `Q ⊩ Q'`.
  open import PolymorphicCalculus.Hypotheses S public
    using (_⊩_≾̂ᵣ_; _⊩_≾̂ₑ_; _⊨ᵍ_; _⊩ᴱ_; _∣_<:̂ᵛ_; _∣_<:̂ᶜ_; VarOK; _⊩ᴴ_[_]; _⊩ᴴ_)
    renaming (Hyps to Hypotheses; _⊩ᴼ_[_] to Gen)
  open import PolymorphicCalculus.Hypotheses.Quantified S public
    using () renaming (QOrd to QuantifiedOrdering)

  -- Proposition (Grade entailment): grade entailment holds of the grade
  -- hypotheses; it is closed under the laws of the grade algebras
  -- (convertibility, transitivity, monotonicity, the morphism, the
  -- joins, the top and the zero-product laws); it contains every true
  -- ordering, at any instance of its effect-grade variables (rule
  -- Truth); it instantiates a quantified hypothesis at any instance of
  -- its rigids (rule Inst); it is stable under substitution; and a
  -- quantified ordering is entailed exactly when it is a semantic
  -- consequence
  open import PolymorphicCalculus.Hypotheses S public
    using ( hypₑ ; hypᵣ ; eqₑ ; eqᵣ ; transₑ ; transᵣ ; monoₑ ; monoᵣ ; map-mono
          ; ⊔-lubₑ ; ⊔-lubᵣ ; ⊔-ubˡₑ ; ⊔-ubˡᵣ ; ⊔-ubʳₑ ; ⊔-ubʳᵣ ; topₑ ; topᵣ
          ; zeroˡₑ ; zeroʳₑ ; zeroˡᵣ ; zeroʳᵣ ; ⊩-substₑ ; ⊩-substᵣ ; ⊩ᴼ⇒⊨ᴼ ; ⊨ᴼ⇒⊩ᴼ )
    renaming (instₑ to Inst; instᵣ to Instʳ; factₑ to Truth; factᵣ to Truthʳ)

  -- Values and computations, among them the handlers `handler H` and
  -- `handle M with V`, and the uses `usedef k` of definitions
  open import PolymorphicCalculus.Syntax.Raw S public
    using (handler; handle_`with_; usedef) renaming (RawV to Value; RawC to Computation)

  -- Programs: sequences of definitions `f = V`
  open import PolymorphicCalculus.Programs.Syntax S public using (Program; ∅ᴾ; _∷ᴾ_)

  -- Definition (Closed instances): closed substitutions, satisfaction,
  -- a quantified ordering at every grade, and satisfiability
  open import PolymorphicCalculus.Hypotheses.Instances S public using (_⊨_; Satisfiable)

  -- Lemma (Soundness of entailment): at a satisfying closed instance, an
  -- entailed ordering holds in the carrier, and an entailed eternality,
  -- subtyping or variable condition holds as the closed relation,
  -- entailment from no hypotheses
  open import PolymorphicCalculus.Hypotheses.Instances S public
    using (sound-≾ᵣ⁰; sound-≾ₑ⁰; ⊨⇒⊩ᴴ)
  open import PolymorphicCalculus.Hypotheses S public using (⊩ᴱ-subst; <:̂ᵛ-subst; VarOK-subst)


------------------------------------------------------------------------
-- Type system

module TypeSystem (S : LanguageSpec) where

  -- Typing judgements `Q | Γ ⊢ V : X` and `Q | Γ ⊢ M : C`, as intrinsically
  -- typed derivations; a typing of a raw term is a derivation erasing to it
  -- (`⌊_⌋ᵛ`, `⌊_⌋ᶜ`). The typing rules in which grades play a role; Unbox
  -- takes a resource value, a variable under annotations, of the judgement
  -- `Q | Γ ⊢ V ↪[ρ'] z : [ρ]X`, which erases to the value (`⌊_⌋ʳ`). Rule
  -- UseDef instantiates a scheme of the program context, with no lock
  -- condition.
  open import PolymorphicCalculus.Typing S public
    using (_∣_⊢V⦂_; _∣_⊢C⦂_; _∣_⊢↪[_]_⦂[_]_)
    renaming ( var to Var ; usedef to UseDef ; return to Return ; subC to Sub ; _⨟_ to Let
             ; perform to Perform ; delay to Delay ; box to Box ; unbox to Unbox
             ; handler to Handler ; handle_`with_ to Handle )
  open import PolymorphicCalculus.Typing.Erasure S public using (⌊_⌋ᵛ; ⌊_⌋ᶜ; ⌊_⌋ʳ)

  -- Definition (Type schemes): principal type schemes of values in
  -- program contexts, and typability; those of computations in open
  -- contexts, with a substitution of the context's variables, from which
  -- the former are derived
  open import PolymorphicCalculus.Inference.Principality S public
    using (Typable; Typableᵛ; valueScheme)
    renaming (PrincipalSchemeᵛ to PrincipalTypeScheme; PrincipalScheme to PrincipalTypeSchemeᶜ)

  -- Programs: each definition typable in the program context of those
  -- before it, which binds it to its principal type scheme there
  open import PolymorphicCalculus.Programs.Typing S public using (⊢ᴾ_⦂_; Accepted)

  -- Lemma (Resource values are annotated variables): in a context whose
  -- program context is that of a program, a value of type `[ρ'']X''` is a
  -- resource value reaching `[ρ]X` with `ρ'' ≾ ρ` and `X <: X''`, and with
  -- the value's erasure. Part (1), the inversion of subtyping at a box
  -- type, is `<:̂ᵛ-boxʳ` and `<:̂ᵛ-boxˡ`.
  open import PolymorphicCalculus.Programs.Typing S public using (program-resource-value)
  open import PolymorphicCalculus.Typing.Resources S public using (ResourceValue)
  open import PolymorphicCalculus.Hypotheses S public using (<:̂ᵛ-boxʳ; <:̂ᵛ-boxˡ)


------------------------------------------------------------------------
-- Operational semantics

module OperationalSemantics (S : LanguageSpec) where

  open import PolymorphicCalculus.Syntax.Scopes using (∅ˢ)
  open import PolymorphicCalculus.Syntax.Types S using (OVType; OCType)
  open import PolymorphicCalculus.Syntax.Contexts S using (OCtx)
  open import PolymorphicCalculus.Hypotheses S using (∅ᴴ)
  open import PolymorphicCalculus.Typing S using (_∣_⊢V⦂_; _∣_⊢C⦂_)

  -- Scope-closed typing `Γ ⊢ V : X` and `Γ ⊢ M : C`, over the empty
  -- scope and under no hypotheses
  ScopeClosedᵛ : ∀ {n} → OCtx ∅ˢ n → OVType ∅ˢ → Set
  ScopeClosedᵛ Γ X = ∅ᴴ ∣ Γ ⊢V⦂ X

  ScopeClosedᶜ : ∀ {n} → OCtx ∅ˢ n → OCType ∅ˢ → Set
  ScopeClosedᶜ Γ C = ∅ᴴ ∣ Γ ⊢C⦂ C

  -- Run-time terms: raw terms without grades and type annotations, and
  -- their scope-closed typing, a scope-closed derivation erasing to the
  -- term
  open import PolymorphicCalculus.Syntax.Run S public using (RunV; RunC; eraseᵛ; eraseᶜ)
  open import PolymorphicCalculus.Typing.ScopeClosed S public using (_⊢ᵛ_⦂_; _⊢ᶜ_⦂_)

  -- States and state typings: the context of a state, a state typing
  -- typing its state, extensions of states and of state typings, and the
  -- grade of the passages an extension adds
  open import PolymorphicCalculus.OperationalSemantics.State S public
    using (State; StateTyping; ctx; Types; _≤ₛ_; δₛ; _⊆[_]_)

  -- The reduction rules for delays, resources and effect handling, on
  -- run-time terms; HANDLE-OP leaves the clause's grade variable
  -- uninstantiated
  open import PolymorphicCalculus.OperationalSemantics.Reduction S public
    using (Step; ⟨_∣_⟩↝⟨_∣_⟩; DELAY; BOX; UNBOX; SEQ-OP; HANDLE-RET; HANDLE-OP)

  -- The remaining rules. CMP decides a comparison by the structural order
  -- on the data its operands denote (`compareᴰ`).
  open import PolymorphicCalculus.OperationalSemantics.Reduction S public
    using ( APP ; MATCH ; CMP ; IF-TRUE ; IF-FALSE ; CASEℕ-ZERO ; CASEℕ-SUCC
          ; RECℕ-ZERO ; RECℕ-SUCC ; CASE-INL ; CASE-INR ; CASEL-NIL ; CASEL-CONS
          ; RECL-NIL ; RECL-CONS ; SEQ-RET ; SEQ-STEP ; HANDLE-STEP ; compareᴰ )


------------------------------------------------------------------------
-- Instantiation and type safety

module InstantiationAndTypeSafety (S : LanguageSpec) where

  -- Erasure `⌊ M[δ] ⌋`: the run-time term of the raw term at an instance,
  -- its annotations dropped and the definitions of the program
  -- substituted (`⟦_⟧ᴾ`), in the context without its program context
  open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S public using (_[_]ᴿᶜ)
  open import PolymorphicCalculus.Syntax.Run S public using (eraseᶜ)
  open import PolymorphicCalculus.Programs.Syntax S public using (⟦_⟧ᴾ; ⌊_⌋ᴾᵛ; ⌊_⌋ᴾᶜ)
  open import PolymorphicCalculus.Programs.Substitution S public using (local)

  -- Theorem (Instantiation), into the scope-closed typing, at the closed
  -- instances `δ ⊨ Q`, in a typed program; handler clauses stay typed
  -- at their variables
  open import PolymorphicCalculus.Programs.Instantiation S public
    using (instantiation; instantiationᵛ)

  -- Theorem (Type safety): a finished term, or a step preserving the
  -- typing in an extension of the state typing
  open import PolymorphicCalculus.OperationalSemantics.Reduction S public using (Final)
  open import PolymorphicCalculus.OperationalSemantics.TypeSafety S public
    using (type-safety; Preserved; progress; preservation)

  -- Theorem (Termination), from the empty state; the multi-step
  -- reduction `⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩`
  open import PolymorphicCalculus.OperationalSemantics.Termination.Reducibility S public using (MultiStep)
  open import PolymorphicCalculus.OperationalSemantics.Termination S public using (Halts; termination)

  -- Corollary (Programs): the instances of a term typed in the program
  -- context of a typed program are typed in the context of the empty
  -- state, and halt
  open import PolymorphicCalculus.Programs.Instantiation S public using (programs)


------------------------------------------------------------------------
-- Type inference

module TypeInference (S : LanguageSpec) (hints : SystemHints (LanguageSpec.Grades S))
                     (opEnum : OpEnum S) where

  -- Definition (Constraints): constraints, solutions, and generation
  open import PolymorphicCalculus.Inference.Constraints.Syntax S public using (Constraint)
  open import PolymorphicCalculus.Inference.Constraints.Satisfaction S public
    using (_⊨[_]_)
  open import PolymorphicCalculus.Inference.Generate S public using (genV; genC)

  -- Theorem (Constraint generation)
  open import PolymorphicCalculus.Inference.Completeness S public
    using () renaming (charC to constraint-generation; charV to constraint-generationᵛ)

  -- Theorem (Solving): the interface of a principal solver, the solver, and
  -- that it is not stuck on constraints without `∀`
  open import PolymorphicCalculus.Inference.Solver S public using (Solver)
  open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum public
    using () renaming (solver to solving; runSolver-rigidFree to solving-not-stuck)

  -- Theorem (Type inference), for values in program contexts; `stuck`
  -- only for values with handlers or using a definition whose scheme has
  -- quantified hypotheses (`NoRigidᵛ`)
  open import PolymorphicCalculus.Inference.Principality S public using (typableᵛ-⇔)
  open import PolymorphicCalculus.Inference.Generate S public using (NoRigidᵛ; NoRigidᶜ)
  open import PolymorphicCalculus.Inference.Values S hints opEnum public
    using ( Inferenceᵛ; inferᵛ; inferᵛ-typed; inferᵛ-untypable; inferᵛ-noRigid
          ; inferᵛ-handlerFree )

  -- The same for computations in open contexts
  open import PolymorphicCalculus.Inference.Principality S public
    using (Inference; typable-⇔)
  open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum public
    using (infer; infer-typed; infer-untypable; infer-noRigid; infer-handlerFree)

  -- Corollary (Completeness), for scope-closed typings of values in any
  -- program context, the empty one among them
  open import PolymorphicCalculus.Inference.Values S hints opEnum public using (completenessᵛ)

  -- The same for computations in contexts over the empty scope
  open import PolymorphicCalculus.Inference.ScopeClosed S hints opEnum public using (completeness)

  -- Checking a program: each definition inferred in the program context
  -- of those before it, its scheme added to it
  open import PolymorphicCalculus.Programs.Checking S hints opEnum public
    using (Checked; checkProgram)


------------------------------------------------------------------------
-- Examples of grade algebras and grade systems

module GradeAlgebraExamples where

  -- Time: grades over ℕ and over ℚ≥0, and the morphisms from the discrete
  -- to the dense grades
  open import Grades.Examples.Time.Intervals public
    using () renaming (intervals to time-domain-intervals)
  open import Grades.Examples.Time.Dense.LeftSidedCut public
    using (left-sided→dense-cut)
  open import Grades.Examples.Time.Dense.RightSidedCut public
    using (right-sided→dense-cut)
  open import Grades.Examples.Time.Dense.TwoSided public using (two-sided→dense)

  -- Operation counts and lattices
  open import Grades.Examples.Counts.Power public using (power)
  open import Grades.Examples.Counts.AtMost public using (at-most-counts)
  open import Grades.Examples.Counts.AtLeast public
    using (at-least-counts; at-least-counts-with-⊤)
  open import Grades.Examples.SecurityLevel public
    using (LevelLattice; level-grade; two-point-levels; taint-sets)

  -- Regular expression grades: lower and upper bounds and intervals over
  -- ℚ≥0, and over ℕ
  open import Grades.Examples.Traces.Rigid.Rational.LeftSided public
    using () renaming (left-sided to regular-lower-bounds)
  open import Grades.Examples.Traces.Rigid.Rational.RightSided public
    using () renaming (right-sided to regular-upper-bounds)
  open import Grades.Examples.Traces.Rigid.Rational.TwoSided public
    using () renaming (two-sided to regular-intervals)
  open import Grades.Examples.Traces.Rigid.Regular.LeftSided public
    using () renaming (left-sided to discrete-regular-lower-bounds)
  open import Grades.Examples.Traces.Rigid.Regular.RightSided public
    using () renaming (right-sided to discrete-regular-upper-bounds)
  open import Grades.Examples.Traces.Rigid.Regular.TwoSided public
    using () renaming (two-sided to discrete-regular-intervals)

  -- Trace grades with time budgets: timed traces; the allowance and
  -- coverage orders, decidable partial orders monotone for sequencing
  open import Grades.Traces.Base public using (Trace)
  open import Grades.Traces.Allowance.Core public
    using (_≼ᵃ[_]_; _≼ᵃ_; nil; keep; skip-op; bank-delay; use-delay; use-op)
  open import Grades.Traces.Coverage.Core public
    using (_≼ᶜ[_]_; _≼ᶜ_) renaming (nil to nilᶜ; keep to keepᶜ; pay-op to pay-opᶜ
                                  ; del-delay to del-delayᶜ; use-delay to use-delayᶜ)
  open import Grades.Traces.Allowance.AsOrder public using (allowancePartialOrder)
  open import Grades.Traces.Coverage.AsOrder public using (coveragePartialOrder)

  -- The trace grade algebras
  open import Grades.Examples.Traces.Subsets.RightSided public
    using () renaming (right-sided to exact-run-sets)
  open import Grades.Examples.Traces.Timed.LeftSided public
    using () renaming (left-sided to lower-trace-bounds)
  open import Grades.Examples.Traces.Timed.RightSided public
    using () renaming (right-sided to upper-trace-bounds)
  open import Grades.Examples.Traces.Timed.TwoSided public
    using () renaming (two-sided to trace-intervals)
  open import Grades.Examples.Traces.Regular.RightSided public
    using () renaming (right-sided to regular-trace-languages)

  -- Grade systems with two different grade algebras
  open import Grades.Examples.System.Identity public using (identityGradeSystem)
  open import Grades.Examples.System.IntervalsToLeftSidedIntervals public
    using (twoSidedIntervalsToLeftSidedIntervalsGradeSystem)
  open import Grades.Examples.Time.Dense.RightSidedCut public
    using () renaming (two-sided→cut to intervals→upper-bounds)
  open import Grades.Examples.System.Traces.Timed.LeftSided public
    using (tracesToLeftSidedIntervalsGradeSystem)
  open import Grades.Examples.System.Traces.Timed.RightSided public
    using (tracesToRightSidedIntervalsGradeSystem)
  open import Grades.Examples.System.Traces.Timed.TwoSided public
    using (tracesToTwoSidedIntervalsGradeSystem)
  open import Grades.Examples.System.Traces.Subsets.RightSided public
    using (subsetsToRightSidedIntervalsGradeSystem)
  open import Grades.Examples.System.Counts.Subsets.AtMost public
    using (subsetsToAtMostCountsGradeSystem)
  open import Grades.Examples.System.Counts.Subsets.AtLeast public
    using (subsetsToAtLeastCountsGradeSystem)
  open import Grades.Examples.System.Counts.Timed.LeftSided public
    using (leftSidedToAtLeastCountsGradeSystem)
  open import Grades.Examples.System.Product.LeftSidedTimeLevel public
    using (embargo-and-taint; embargo; taint)

  -- The three absences of grade algebra morphisms
  open import Grades.Examples.System.Counts.Timed.RightSided public
    using (erases; miscounts)
  open import Grades.Examples.System.Counts.Time public
    using ( no-projection ; no-at-most-counts→right-sided-intervals
          ; no-at-least-counts→left-sided-intervals )
  open import Grades.Examples.Traces.Regular.Subsets public
    using (lang; lang-mono; lang-reflect; no-morphism)


------------------------------------------------------------------------
-- The calculus with grade variables

module CalculusWithGradeVariables (S : LanguageSpec) where

  -- Definition (Signatures): a grade system, base types and operations.
  -- Comparisons are decided by the structural order on the data the
  -- operands denote (`compareᴰ`), from a strict total order on each
  -- eternal base type.
  open import Language.Spec public using (LanguageSpec; withoutBaseTypes)
  open import Language.Operations public using (Operations)
  open import Language.BaseTypes public using (BaseTypes; noBaseTypes)
  open import Language.Comparisons public using () renaming (Cmp to Comparison)
  open import PolymorphicCalculus.OperationalSemantics.Reduction S public using (compareᴰ)

  -- Raw values and computations
  open import PolymorphicCalculus.Syntax.Raw S public using (RawV; RawC)

  -- Entailment: convertibility, entailment from no hypotheses both ways,
  -- and the rules, those of grade entailment its properties. The rules
  -- are named for effect grades; the resource rules carry a subscript
  -- `ᵣ`. Var-Et has one rule per disjunct; Var-Hyp meets a disjunction
  -- hypothesis at a grade below its own; the variable condition is
  -- closed under subtyping in both directions (Var-Sub-L, Var-Sub-R),
  -- products, sums and lists (Var-Prod, Var-Sum, Var-List), and joins
  -- of grades (Var-Join).
  open import PolymorphicCalculus.Hypotheses S public
    using (_≡̂ₑ_; _≡̂ᵣ_; _≡̂ᵛ_; _⊩ᵗᵛ_≾_)
    renaming ( hypₑ to Hyp ; hypᵣ to Hypᵣ ; eqₑ to Conv ; eqᵣ to Convᵣ
             ; monoₑ to Mono ; monoᵣ to Monoᵣ ; map-mono to Map
             ; zeroˡₑ to Id-Prodˡ ; zeroʳₑ to Id-Prodʳ
             ; zeroˡᵣ to Id-Prodˡᵣ ; zeroʳᵣ to Id-Prodʳᵣ
             ; tvarₛ to Sub-Var
             ; et-ok to Var-Etˡ ; ≾ᵘ-ok to Var-Etʳ ; hyp-ok to Var-Hyp
             ; subˡ-ok to Var-Sub-L ; subʳ-ok to Var-Sub-R
             ; _|×|-ok_ to Var-Prod ; _|+|-ok_ to Var-Sum ; |List|-ok to Var-List
             ; ⊔-ok to Var-Join
             ; atomₑ to Const ; atomᵣ to Constᵣ
             ; transₑ to Trans ; transᵣ to Transᵣ
             ; ⊔-lubₑ to Lub ; ⊔-lubᵣ to Lubᵣ
             ; ⊔-ubˡₑ to Ub-L ; ⊔-ubˡᵣ to Ub-Lᵣ ; ⊔-ubʳₑ to Ub-R ; ⊔-ubʳᵣ to Ub-Rᵣ
             ; topₑ to Top ; topᵣ to Topᵣ ; minₑ to Least ; minᵣ to Leastᵣ
             ; plusₑ to Plus ; plusᵣ to Plusᵣ
             ; indˡₑ to Ind-L ; indˡᵣ to Ind-Lᵣ ; indʳₑ to Ind-R ; indʳᵣ to Ind-Rᵣ
             ; et-hyp to Et-Hyp ; et-subˡ to Et-Sub-L ; et-subʳ to Et-Sub-R
             ; Unitₑ to Et-Unit ; Boolₑ to Et-Bool ; Natₑ to Et-Nat ; Emptyₑ to Et-Empty
             ; Baseₑ to Et-Base
             ; _|×|ₑ_ to Et-Prod ; _|+|ₑ_ to Et-Sum ; |List|ₑ to Et-List
             ; Unitₛ to S-Unit ; Boolₛ to S-Bool ; Natₛ to S-Nat ; Emptyₛ to S-Empty
             ; Baseₛ to S-Base
             ; _|×|ₛ_ to S-Prod ; _|+|ₛ_ to S-Sum ; |List|ₛ to S-List
             ; _⇒ₛ_ to S-Fun ; [_]ₛ_ to S-Box ; _‼ₛ_ to S-Comp ; _⇛ₛ_ to S-Handler )

  -- The remaining typing rules. Const-Base types the constants of a base
  -- type.
  open import PolymorphicCalculus.Typing S public
    using ()
    renaming ( ⋆ to Unit ; true to True ; false to False ; zero to Zero ; succ to Succ
             ; ⦉_,_⦊ to Pair ; inl to Inl ; inr to Inr ; nil to Nil ; cons to Cons
             ; lam to Fun ; subV to Sub-V ; annᵛ to Ann-V ; _·_ to App
             ; match_`in_ to Match ; absurd to Absurd ; cmp to Cmp
             ; if_`then_`else_ to If ; caseℕ_`zero_`succ_ to Case-Nat ; recℕ to Rec-Nat
             ; case+_`inl_`inr_ to Case-Sum ; caseL_`nil_`cons_ to Case-List
             ; recL to Rec-List ; annᶜ to Ann-C ; const to Const-Base )


------------------------------------------------------------------------
-- Further results

module FormalisedResults (S : LanguageSpec) (hints : SystemHints (LanguageSpec.Grades S))
                         (opEnum : OpEnum S) where

  -- Entailment is stable under substitution and weakening, and the side
  -- condition of the variable rule under equivalence of the type;
  -- convertible expressions have equivalent values
  open import PolymorphicCalculus.Hypotheses S public
    using (⊩-substᵣ; ⊩-substₑ; ⊩ᴱ-subst; <:̂ᵛ-subst; VarOK-subst; ⊩-wkᵉᵣ; ⊩-wkᵉₑ; VarOK-≃)
  open import PolymorphicCalculus.Hypotheses.Instances S public using (val-≡̂ᵣ; val-≾ᵣ)

  -- Substitution of types and grades in typings, and the instance of a
  -- handler clause at a grade for its variable; renaming and, under no
  -- hypotheses, substitution of term variables; inversion
  open import PolymorphicCalculus.Typing.GradeSubstitution S public
    using (substᵛ; substᶜ; instantiate-clause)
  open import PolymorphicCalculus.Typing.Renaming S public using (Ren; rename-v; rename-c; eternal-v)
  open import PolymorphicCalculus.Typing.Substitution S public using (Drop; sub-v; sub-c)
  open import PolymorphicCalculus.Typing.Inversion S public using (invV; invC)

  -- Conversion of a context's types: under any hypotheses, to equivalent
  -- types; under hypotheses with no disjunction, to subtypes
  open import PolymorphicCalculus.Typing.Conversion S public
    using (Conversion; equivalence; narrowing; CtxRel; conv-v; conv-c)

  -- Resource values: under a program context whose schemes have
  -- non-resource types, a value of box type is a resource value
  open import PolymorphicCalculus.Typing.Resources S public
    using (NonResourceDefs; resource-value; res-collapse)

  -- Instantiation of the scope alone, keeping the program context; the
  -- substitution of closed typings of the definitions for their uses
  -- (the substitution lemma for UseDef), which a typed program provides
  open import PolymorphicCalculus.Typing.Instantiation S public
    using (scope-instantiation; scope-instantiationᵛ)
  open import PolymorphicCalculus.Programs.Substitution S public using (DefsEnv; sdef-v; sdef-c)
  open import PolymorphicCalculus.Programs.Typing S public using (programEnv)

  -- Reducibility: the logical relation on run-time terms over states,
  -- and its fundamental lemma
  open import PolymorphicCalculus.OperationalSemantics.Termination.Reducibility S public
    using (VRed; VRedᵍ; CRed; cred-seq; cred-handle)
  open import PolymorphicCalculus.OperationalSemantics.Termination S public using (fund-v; fund-c)

  -- Open subtyping is a preorder and reflects eternality
  open import PolymorphicCalculus.Hypotheses S public
    using (<:̂ᵛ-refl; <:̂ᵛ-trans; <:̂ᵛ-eternalˡ; <:̂ᵛ-eternalʳ)

  -- Constraint generation is sound and complete; a use of a definition
  -- generates an instance of its scheme, its hypotheses as a constraint
  open import PolymorphicCalculus.Inference.Soundness S public using (soundV; soundC)
  open import PolymorphicCalculus.Inference.Completeness S public using (completeV; completeC)
  open import PolymorphicCalculus.Inference.Constraints.Schemes S public
    using (hypsᶜ; instᶜ; instᶜ-sound; instᶜ-complete)

  -- A solver meeting the interface gives principal solutions; the solver
  -- meets it
  open import PolymorphicCalculus.Inference.Principality S public
    using (principalSolution; principal-inst; typable-unconditional)
  open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum public
    using ( runSolver-sound ; runSolver-principal ; runSolver-complete
          ; runSolver-refutes ; infer-unconditional ; infer-complete
          ; check ; check-established ; check-untypable ; check-complete
          ; check-handlerFree )

