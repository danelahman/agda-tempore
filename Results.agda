------------------------------------------------------------------------
-- Overview of the main definitions and results
--
-- One entry per construct, rule, definition, lemma and theorem, named by
-- its title: grade systems; the calculus with type and grade variables,
-- its type system, semantics and type inference; the closed calculus and
-- its semantics. The items not yet formalised are listed at the end.
--
-- The calculus is parameterised by a `LanguageSpec` (a grade system, base
-- types and an operation signature); inference also takes an enumeration
-- of the operations (`OpEnum`).
------------------------------------------------------------------------

module Results where

open import Language.Spec using (LanguageSpec)
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)


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
  open import OpenCalculus.Syntax.Scopes public using (Scope; TyVar; RVar; EVar)
  open import OpenCalculus.Syntax.Grades S public
    using () renaming (EExp to EffectGradeExpr; RExp to ResourceGradeExpr)

  -- Ground types: unit, booleans, natural numbers, the empty type,
  -- products, sums, lists, graded modal types and base types
  open import Language.Types S public using () renaming (GType to GroundType)

  -- Value and computation types, among them the handler types `C ⇛ D`
  open import OpenCalculus.Syntax.Types S public
    using (_⇛_) renaming (OVType to ValueType; OCType to ComputationType)

  -- Contexts, and the lookup `x : X ∈_ρ Γ`
  open import OpenCalculus.Syntax.Contexts S public
    using (_∈̂[_]_) renaming (OCtx to Context)

  -- Typing hypotheses. Definition (Entailment): orderings, eternality,
  -- subtyping, the disjunction of the variable rule, and `Q ⊩ Q'[δ]`.
  open import OpenCalculus.Hypotheses S public
    using (_⊩_≾̂ᵣ_; _⊩_≾̂ₑ_; _⊩ᴱ_; _∣_<:̂ᵛ_; _∣_<:̂ᶜ_; VarOK; _⊩ᴴ_[_])
    renaming (Hyps to Hypotheses)

  -- Values and computations, among them the handlers `handler H` and
  -- `handle M with V`
  open import OpenCalculus.Syntax.Raw S public
    using (handler; handle_`with_) renaming (RawV to Value; RawC to Computation)

  -- Definition (Closed instances)
  open import Bridge.Instantiation.Types S public
    using () renaming (DInst to ClosedInstance)
  open import Bridge.Instantiation.Judgements S public using (_⊨ᴰ_)
  open import OpenCalculus.Hypotheses.Instances S public using (Satisfiable)

  -- Lemma (Soundness of entailment)
  open import Bridge.Instantiation.Judgements S public
    using (sound-≾ᵣ; sound-≾ₑ; sound-⊩ᴱ; sound-<:ᵛ; sound-<:ᶜ; sound-VarOK)


------------------------------------------------------------------------
-- Type system

module TypeSystem (S : LanguageSpec) where

  -- Typing judgements `Q | Γ ⊢ V : X` and `Q | Γ ⊢ M : C`, as intrinsically
  -- typed derivations; a typing of a raw term is a derivation erasing to it
  -- (`⌊_⌋ᵛ`, `⌊_⌋ᶜ`). The typing rules in which grades play a role; Unbox
  -- takes a variable.
  open import OpenCalculus.Typing S public
    using (_∣_⊢V⦂_; _∣_⊢C⦂_)
    renaming ( var to Var ; return to Return ; subC to Sub ; _⨟_ to Let
             ; perform to Perform ; delay to Delay ; box to Box ; unbox to Unbox
             ; handler to Handler ; handle_`with_ to Handle )
  open import OpenCalculus.Typing.Erasure S public using (⌊_⌋ᵛ; ⌊_⌋ᶜ)

  -- Definition (Type schemes): principal schemes of computations in open
  -- contexts, with a substitution of the context's variables and
  -- obligations
  open import OpenCalculus.Inference.Principality S public
    using (Typable) renaming (PrincipalScheme to PrincipalTypeScheme)


------------------------------------------------------------------------
-- Operational semantics

module OperationalSemantics (S : LanguageSpec) where

  open import OpenCalculus.Syntax.Scopes using (∅ˢ)
  open import OpenCalculus.Syntax.Types S using (OVType; OCType)
  open import OpenCalculus.Syntax.Contexts S using (OCtx)
  open import OpenCalculus.Hypotheses S using (∅ᴴ)
  open import OpenCalculus.Typing S using (_∣_⊢V⦂_; _∣_⊢C⦂_)

  -- Scope-closed typing `Γ ⊢ V : X` and `Γ ⊢ M : C`
  ScopeClosedᵛ : ∀ {n} → OCtx ∅ˢ n → OVType ∅ˢ → Set
  ScopeClosedᵛ Γ X = ∅ᴴ ∣ Γ ⊢V⦂ X

  ScopeClosedᶜ : ∀ {n} → OCtx ∅ˢ n → OCType ∅ˢ → Set
  ScopeClosedᶜ Γ C = ∅ᴴ ∣ Γ ⊢C⦂ C

  -- Run-time terms: raw terms without grades and type annotations, and
  -- their scope-closed typing, a scope-closed derivation erasing to the
  -- term
  open import OpenCalculus.Syntax.Run S public using (RunV; RunC; eraseᵛ; eraseᶜ)
  open import OpenCalculus.Typing.ScopeClosed S public using (_⊢ᵛ_⦂_; _⊢ᶜ_⦂_)

  -- States and state typings: the context of a state, a state typing
  -- typing its state, extensions of states and of state typings, and the
  -- grade of the passages an extension adds
  open import OpenCalculus.Semantics.States S public
    using (State; StateTyping; ctx; Types; _≤ₛ_; δₛ; _⊆[_]_)

  -- The reduction rules for delays, resources and effect handling, on
  -- run-time terms; HANDLE-OP leaves the clause's grade variable
  -- uninstantiated
  open import OpenCalculus.Semantics.Reduction S public
    using (Step; ⟨_∣_⟩↝⟨_∣_⟩; DELAY; BOX; UNBOX; SEQ-OP; HANDLE-RET; HANDLE-OP)

  -- The remaining rules. CMP decides a comparison by the structural order
  -- on the data its operands denote (`compareᴰ`).
  open import OpenCalculus.Semantics.Reduction S public
    using ( APP ; MATCH ; CMP ; IF-TRUE ; IF-FALSE ; CASEℕ-ZERO ; CASEℕ-SUCC
          ; RECℕ-ZERO ; RECℕ-SUCC ; CASE-INL ; CASE-INR ; CASEL-NIL ; CASEL-CONS
          ; RECL-NIL ; RECL-CONS ; SEQ-RET ; SEQ-STEP ; HANDLE-STEP ; compareᴰ )


------------------------------------------------------------------------
-- Instantiation and type safety

module InstantiationAndTypeSafety (S : LanguageSpec) (opEnum : OpEnum S) where

  -- Erasure `⌊ M[δ] ⌋`: the run-time term of the raw term at an instance,
  -- its annotations dropped
  open import OpenCalculus.Syntax.Raw.Subst S public using (_[_]ᴿᶜ)
  open import OpenCalculus.Syntax.Run S public using (eraseᶜ)

  -- Theorem (Instantiation), into the scope-closed typing, at the closed
  -- instances `δ ⊨ Q ∣ []`; handler clauses stay typed at their variables
  open import OpenCalculus.Typing.Instantiation S public
    using (instantiation; instantiationᵛ)

  -- Theorem (Type safety): a finished term, or a step preserving the
  -- typing in an extension of the state typing
  open import OpenCalculus.Semantics.TypeSafety S public
    using (type-safety; Final; Preserved; progress; preservation)

  -- Theorem (Termination), of the closed calculus
  open import ClosedCalculus.Adequacy.Evaluation S public using (Halts)
  open import ClosedCalculus.Adequacy.Normalization S public
    using () renaming (halts to termination)

  -- Corollary (Programs): for a term whose handlers are second-class, an
  -- established check gives a closed typing at an instance, and that
  -- program halts
  open import Bridge.Instantiation.Inference S opEnum public
    using () renaming (check-program to programs)


------------------------------------------------------------------------
-- Type inference

module TypeInference (S : LanguageSpec) (opEnum : OpEnum S) where

  -- Definition (Constraints): constraints, solutions, solutions with
  -- obligations, and generation
  open import OpenCalculus.Inference.Constraints.Syntax S public using (Constraint)
  open import OpenCalculus.Inference.Constraints.Satisfaction S public
    using (_⊨[_]_; _⊨[_∣_]_)
  open import OpenCalculus.Inference.Generate S public using (genV; genC)

  -- Theorem (Constraint generation)
  open import OpenCalculus.Inference.Completeness S public
    using () renaming (charC to constraint-generation; charV to constraint-generationᵛ)

  -- Theorem (Solving): the interface of a principal solver, the solver, and
  -- that it is not stuck on constraints without `∀`
  open import OpenCalculus.Inference.Solver S public using (Solver)
  open import OpenCalculus.Inference.SolverImpl S opEnum public
    using () renaming (solver to solving; runSolver-rigidFree to solving-not-stuck)

  -- Theorem (Type inference), for computations in open contexts
  open import OpenCalculus.Inference.Principality S public
    using (Inference; typable-⇔)
  open import OpenCalculus.Inference.SolverImpl S opEnum public
    using (infer; infer-typed; infer-untypable; infer-handlerFree)

  -- Corollary (Completeness), for annotation-free terms in contexts with
  -- no handler type, with respect to closed typings whose handlers are
  -- uniform, the handler of each `handle` a handler
  open import Bridge.Instantiation.Types S public using (NoHandlerTypeᶜᵗˣ)
  open import Bridge.Instantiation.Completeness S opEnum public
    using (UniformTyping; infer-principal; infer-untypableᴰ)


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

  -- Definition (Signatures). The comparisons are decided by a strict
  -- total order on the data of each eternal type (`compareᵈ`), from one
  -- on each base type. The calculus is the instance without base types,
  -- over a grade system and an operation signature.
  open import Language.Spec public using (LanguageSpec; withoutBaseTypes)
  open import Language.Operations public using (Operations)
  open import Language.BaseTypes public using (BaseTypes; noBaseTypes)
  open import Language.Comparisons public using () renaming (Cmp to Comparison)
  open import ClosedCalculus.Syntax.Data S public using (compareᵈ)

  -- Raw values and computations
  open import OpenCalculus.Syntax.Raw S public using (RawV; RawC)

  -- Entailment: convertibility and the rules. The rules are named for
  -- effect grades; the resource rules carry a subscript `ᵣ`. Var-Et has one
  -- rule per disjunct.
  open import OpenCalculus.Hypotheses S public
    using (_≡̂ₑ_; _≡̂ᵣ_; _≡̂ᵛ_; _⊩ᵗᵛ_≾_)
    renaming ( hypₑ to Hyp ; hypᵣ to Hypᵣ ; eqₑ to Conv ; eqᵣ to Convᵣ
             ; monoₑ to Mono ; monoᵣ to Monoᵣ ; map-mono to Map
             ; zeroˡₑ to Id-Prodˡ ; zeroʳₑ to Id-Prodʳ
             ; zeroˡᵣ to Id-Prodˡᵣ ; zeroʳᵣ to Id-Prodʳᵣ
             ; tvarₛ to Sub-Var
             ; et-ok to Var-Etˡ ; ≾ᵘ-ok to Var-Etʳ ; hyp-ok to Var-Hyp
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
  open import OpenCalculus.Typing S public
    using ()
    renaming ( ⋆ to Unit ; true to True ; false to False ; zero to Zero ; succ to Succ
             ; ⦉_,_⦊ to Pair ; inl to Inl ; inr to Inr ; nil to Nil ; cons to Cons
             ; lam to Fun ; subV to Sub-V ; annᵛ to Ann-V ; _·_ to App
             ; match_`in_ to Match ; absurd to Absurd ; cmp to Cmp
             ; if_`then_`else_ to If ; caseℕ_`zero_`succ_ to Case-Nat ; recℕ to Rec-Nat
             ; case+_`inl_`inr_ to Case-Sum ; caseL_`nil_`cons_ to Case-List
             ; recL to Rec-List ; annᶜ to Ann-C ; const to Const-Base )


------------------------------------------------------------------------
-- The closed calculus

module TheClosedCalculus (S : LanguageSpec) where

  -- Closed types, contexts, eternal types, the grade of a context, and
  -- variables under locks
  open import Language.Types S public
    using (GType; VType; CType; Eternal; type-of-gtype)
    renaming ( Unitₑ to Et-Unit ; Boolₑ to Et-Bool ; Natₑ to Et-Nat ; Emptyₑ to Et-Empty
             ; Baseₑ to Et-Base
             ; _|×|ₑ_ to Et-Prod ; _|+|ₑ_ to Et-Sum ; |List|ₑ to Et-List )
  open import ClosedCalculus.Syntax.Contexts S public
    using (Ctx; ctx-grade; _∈[_]_; Hd; Tl-∷; Tl-⟨⟩)

  -- Subtyping
  open import ClosedCalculus.Syntax.Subtyping S public
    using (_<:ᵛ_; _<:ᶜ_)
    renaming ( Unitₛ to S-Unit ; Boolₛ to S-Bool ; Natₛ to S-Nat ; Emptyₛ to S-Empty
             ; Baseₛ to S-Base
             ; _|×|ₛ_ to S-Prod ; _|+|ₛ_ to S-Sum ; |List|ₛ to S-List
             ; _⇒ₛ_ to S-Fun ; [_]ₛ_ to S-Box ; _‼ₛ_ to S-Comp )

  -- Closed typing of values and of computations
  open import ClosedCalculus.Syntax.Terms S public
    using (_⊢V⦂_; _⊢C⦂_)
    renaming ( var to Var ; ⋆ to Unit ; true to True ; false to False ; zero to Zero
             ; succ to Succ ; ⦉_,_⦊ to Pair ; inl to Inl ; inr to Inr ; nil to Nil
             ; cons to Cons ; lam to Fun ; subV to Sub-V ; const to Const-Base
             ; return to Return ; _⨟_ to Let ; _·_ to App ; match_`in_ to Match
             ; absurd to Absurd ; cmp to Cmp ; if_`then_`else_ to If
             ; caseℕ_`zero_`succ_ to Case-Nat ; recℕ to Rec-Nat
             ; case+_`inl_`inr_ to Case-Sum ; caseL_`nil_`cons_ to Case-List
             ; recL to Rec-List ; perform to Perform ; delay to Delay
             ; handle_`with_`in to Handle ; box to Box ; unbox to Unbox ; subC to Sub-C )

  -- Lemma (Subtyping): a preorder, antisymmetric where the grade orders
  -- are, reflecting eternality
  open import ClosedCalculus.Syntax.Subtyping S public
    using (<:ᵛ-refl; <:ᵛ-trans; <:ᵛ-antisym; <:ᵛ-irrelevant; <:ᵛ-eternalˡ)

  -- Definition (Renamings)
  open import ClosedCalculus.Syntax.Renamings.Base S public
    using ( Ren ; EternalCtx ; id-ren ; _∘ʳ_ ; wk-ren ; var-ren ; ⟨⟩-η-ren ; ⟨⟩-η⁻¹-ren
          ; ⟨⟩-μ-ren ; ⟨⟩-≤-ren ; ⟨⟩-ext-ctx ; cong-∷-ren ; cong-⟨⟩-ren ; exch-ren )

  -- Theorem (Renaming); Corollary (Structural rules) is its instances at
  -- the generators. Lemma (Values under locks), part 3 (Unbox-Val).
  open import ClosedCalculus.Syntax.RenActions S public
    using (V-rename; C-rename; unbox-val)

  -- Lemma (Values under locks), parts 1 and 2
  open import ClosedCalculus.Syntax.Terms S public
    using (eternal-val-ext; grad-typ⇒var<:)

  -- Theorem (Substitution)
  open import ClosedCalculus.Syntax.Substitutions S public using (_[_↦_]v; _[_↦_]c)

  -- Lemma (Context subsumption)
  open import ClosedCalculus.Syntax.Substitutions.Subsumption S public using (subCtx)

  -- Lemma (Subsumption at reconciliation points)
  open import ClosedCalculus.Syntax.Normalisation S public
    using (V-normal-form; C-normal-form)


------------------------------------------------------------------------
-- Operational semantics and type safety of the closed calculus

module OperationalSemanticsAndTypeSafety (S : LanguageSpec) where

  -- Definition (States)
  open import ClosedCalculus.OperationalSemantics.State S public
    using (𝕊; ∅; _⟨_⟩ₛ; _∷ₛ_; toCtx; state-grade; _≤ₛ_; ≤ₛ-grade; state-grade-≤ₛ)

  -- Definition (Configurations), and the small-step operational semantics.
  -- CMP reduces a comparison to its boolean; SUB, SUB-APP, SUB-IF,
  -- SUB-CASEℕ and SUB-RECℕ move a subsumption and erase to the identity on
  -- raw terms.
  open import ClosedCalculus.OperationalSemantics.PreservationTheorem S public
    using ( Config ; _↝_
          ; APP ; MATCH ; CMP ; IF-TRUE ; IF-FALSE ; CASEℕ-ZERO ; CASEℕ-SUCC
          ; RECℕ-ZERO ; RECℕ-SUCC ; CASE+ ; CASE-INL ; CASE-INR ; CASEL ; CASEL-NIL
          ; CASEL-CONS ; RECL ; RECL-NIL ; RECL-CONS ; SEQ-RET ; SEQ-OP ; DELAY
          ; HANDLE-RET ; HANDLE-OP ; BOX ; UNBOX ; SEQ-STEP ; HANDLE-STEP
          ; SUB ; SUB-APP ; SUB-IF ; SUB-CASEℕ ; SUB-RECℕ )

  -- Theorem (Preservation)
  open import ClosedCalculus.OperationalSemantics.PreservationTheorem S public
    using (step-extends-state; step-refines-type; step-grade-≾; step-invariants)

  -- Theorem (Progress)
  open import ClosedCalculus.OperationalSemantics.ProgressTheorem S public
    using (Progresses; progress; finality-value; finality-op)

  -- Theorem (Termination)
  open import ClosedCalculus.Adequacy.Evaluation S public using (Halts)
  open import ClosedCalculus.Adequacy.Normalization S public using (halts)

  -- Definition (Top-level semantics); Theorem (Top-level preservation and
  -- progress)
  open import ClosedCalculus.OperationalSemantics.TopLevelOpSemantics S public
    using (TopLevelOpSemantics)
  open import ClosedCalculus.OperationalSemantics.TopLevelPreservationTheorem S public
    using (module PureTopLevelPreservationTheorem)
  open import ClosedCalculus.OperationalSemantics.TopLevelProgressTheorem S public
    using (module PureTopLevelProgressTheorem)


------------------------------------------------------------------------
-- Equational theory and denotational semantics
--
-- The entries over a model take the model's components (`Cat`, `Fut`,
-- `Pst`, `Adj`, `GTy`, `Mon`, `GE`) as their first arguments.

module EquationalTheoryAndDenotationalSemantics (S : LanguageSpec) where

  -- Definition (Equational theory), and its axioms
  open import ClosedCalculus.EquationalTheory.EquationalTheory S public
    using ( _⊢V⦂_==_ ; _⊢C⦂_==_
          ; seq-return ; seq-perform ; seq-delay ; seq-box ; seq-unbox ; seq-eta
          ; seq-assoc ; fun-beta ; fun-eta ; unit-eta ; handle-return ; handle-perform
          ; handle-delay ; handle-box ; handle-unbox ; delay-zero ; delay-delay
          ; unbox-beta ; boxed-not-used ; unbox-not-used ; box-comm ; unbox-comm
          ; box-unbox-comm )

  -- Definition (Models)
  open import ClosedCalculus.DenotationalSemantics.Model.Category public using (Category)
  open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future public
    using (Future)
  open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past public using (Past)
  open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction public
    using (Adjunction)
  open import ClosedCalculus.DenotationalSemantics.Model.Modality.Eternal public
    using (Eternalᵒ)
  open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes S public
    using (GroundTypes)
  open import ClosedCalculus.DenotationalSemantics.Model.GroundEternal public
    using (GroundEternal)
  open import ClosedCalculus.DenotationalSemantics.Model.Monad public using (Monad)

  -- Definition (Interpretation), for derivations whose handlers are uniform
  -- (`Paramᶜ`)
  open import ClosedCalculus.DenotationalSemantics.Interpretation.Types public
    using (⟦_⟧ᵛ; ⟦_⟧ᶜ)
  open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts public
    using (⟦_⟧ᶜᵗˣ)
  open import ClosedCalculus.DenotationalSemantics.Interpretation.Terms public
    using (⟦_⟧ᵛᵗ; ⟦_⟧ᶜᵗ; Paramᵛ; Paramᶜ)

  -- Theorem (Coherence with renaming and substitution)
  open import ClosedCalculus.DenotationalSemantics.Interpretation.RenamingCoherence public
    using (V-rename-nat; C-rename-nat)
  open import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Core public
    using (V-subst-nat; C-subst-nat)

  -- Theorem (Soundness of the equational theory)
  open import ClosedCalculus.EquationalTheory.Soundness public using (soundᵛ; soundᶜ)

  -- Theorem (Soundness of the operational semantics)
  open import ClosedCalculus.OperationalSemantics.Soundness.Preservation public
    using (↝*-⊳)

  -- Definition (Kripke frames and the presheaf model)
  open import ClosedCalculus.DenotationalSemantics.Model.World public using (World)
  open import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Base public
    using (PShCat)
  open import ClosedCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Instance public
    using (PShMonad)

  -- Theorem (Adequacy), for head-faithful models; the presheaf model is
  -- one (`PShHeadFaithful` in `ClosedCalculus.Adequacy.PSh.HeadFaithful`);
  -- the observational corollary is `ClosedCalculus.Adequacy.Equational`.
  open import ClosedCalculus.Adequacy.HeadFaithful public using (HeadFaithful)
  open import ClosedCalculus.Adequacy.Adequacy public using (adequacy)
  import ClosedCalculus.Adequacy.PSh.HeadFaithful
  import ClosedCalculus.Adequacy.Equational


------------------------------------------------------------------------
-- Further results

module FormalisedResults (S : LanguageSpec) (opEnum : OpEnum S) where

  -- Entailment is stable under substitution and weakening; convertible
  -- expressions have equivalent values
  open import OpenCalculus.Hypotheses S public
    using (⊩-substᵣ; ⊩-substₑ; ⊩ᴱ-subst; <:̂ᵛ-subst; VarOK-subst; ⊩-wkᵉᵣ; ⊩-wkᵉₑ)
  open import OpenCalculus.Hypotheses.Instances S public using (val-≡̂ᵣ; val-≾ᵣ)

  -- Substitution of types and grades in typings, and the instance of a
  -- handler clause at a grade for its variable; renaming and, under the
  -- empty hypothesis set, substitution of term variables; inversion
  open import OpenCalculus.Typing.GradeSubstitution S public
    using (substᵛ; substᶜ; instantiate-clause)
  open import OpenCalculus.Typing.Renaming S public using (Ren; rename-v; rename-c; eternal-v)
  open import OpenCalculus.Typing.Substitution S public using (Drop; sub-v; sub-c)
  open import OpenCalculus.Typing.Inversion S public using (invV; invC)

  -- Closed instances of the two kinds correspond
  open import Bridge.Instantiation.Correspondence S public using (⊨⇔⊨ᴰ)

  -- Instantiation into the closed calculus, for terms whose handlers are
  -- second-class, every handler being the handler of a `handle` and every
  -- `handle`'s handler a handler; each handler clause instantiated at
  -- every continuation grade; a value as `return V`. The elaboration
  -- `⌊_⌋ᴿᶜ` forgets annotations, evaluates box grades, and runs
  -- comparisons, values here and computations there, before the
  -- computation whose values they are in.
  open import OpenCalculus.Syntax.Raw S public using (SecondClassᶜ)
  open import Bridge.Instantiation.Terms S public
    using (⌊_⌋ᴿᶜ; instantiateᵛ; instantiateᶜ; instantiateˢᵛ; instantiateˢᶜ)

  -- Open subtyping is a preorder and reflects eternality
  open import OpenCalculus.Hypotheses S public
    using (<:̂ᵛ-refl; <:̂ᵛ-trans; <:̂ᵛ-eternalˡ; <:̂ᵛ-eternalʳ)

  -- Constraint generation is sound and complete
  open import OpenCalculus.Inference.Soundness S public using (soundV; soundC)
  open import OpenCalculus.Inference.Completeness S public using (completeV; completeC)

  -- A solver meeting the interface gives principal solutions; the solver
  -- meets it
  open import OpenCalculus.Inference.Principality S public
    using (principalSolution; principal-inst; typable-unconditional)
  open import OpenCalculus.Inference.SolverImpl S opEnum public
    using ( runSolver-sound ; runSolver-principal ; runSolver-complete
          ; runSolver-refutes ; infer-unconditional ; infer-complete
          ; check ; check-established ; check-untypable ; check-complete
          ; check-handlerFree )

  -- Inference yields closed typings at every instance satisfying the
  -- scheme; completeness and principality for the declarative system
  open import Bridge.Instantiation.Inference S opEnum public
    using (scheme-instantiate; infer-instantiate; check-instantiate)
  open import Bridge.Instantiation.Embedding S public using (Uᶜ; embedᶜ; AnnFreeᶜ)
  open import Bridge.Instantiation.Completeness S opEnum public
    using ( principalᴰ ; infer-principal-typing ; check-principal
          ; check-untypableᴰ )


------------------------------------------------------------------------
-- Not yet formalised
--
--   Handler types, handler values and `handle M with V` in the closed
--   calculus, its semantics and equational theory, where handlers occur in
--   `handle M with H to x in N`; instantiation for terms whose handlers
--   are not second-class.
--   Quantified orderings `∀e. ε ≾ ε'` in hypotheses, with the rules Inst and
--   Gen; solutions and type schemes without separate obligations.
--   Program contexts, the rule Def, type schemes of values, and programs.
--   Unbox on an annotated variable, and Lemma (Resource values are
--   annotated variables) for the calculus with grade variables.
--   Termination of the reduction on run-time terms.
------------------------------------------------------------------------
