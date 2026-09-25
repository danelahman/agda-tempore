# Agda formalisation of a generally graded core language for temporal resources

An Agda formalisation of a (Fitch-style) **generally graded, modally typed,
effectful core language for safe and correct programming with temporal
resources**, i.e., resources that become available only after some amount of
time, events, etc. after being brought into scope, e.g., when an assembly
operation needs to wait for (car) parts to dry after executing a paint
operation, or for some other actions to happen before executing new operations.

This repository builds on two prior formalisations that only modelled discrete
time passage as the means to specify and verify temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources)
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).

In contrast, the core language formalised in this repository can use arbitrary
partially ordered monoids to specify effects and verify temporal properties 
of resources. Furthermore, one can use *different* monoids for grading effects 
and resources, related by a grade morphism, so that an effect grade (e.g., a 
trace or interval of possible execution costs) can be reinterpreted as a resource 
grade (e.g., the amount of time after which a resource becomes available).

The **main features** of this core language are:

- Fitch-style, _temporally-graded modal types_ `[ ρ ]ᵍ A` (on ground types) and
  `[ ρ ] X` (on value types) are used to capture temporal resources, expressing
  that an `A`/`X`-typed value will be available in at most `ρ` time steps, after
  at most `ρ` events, or after some similar resource grade has elapsed.

- A novel notion of _temporally-aware algebraic effects_, where operations'
  specifications include their effect grade, and their continuations know that
  an operation's worth of additional time, events, etc. has happened before
  they start executing, making it possible to safely access further temporal
  resources in the continuation.

- _Effect handlers_, also temporally-aware, that have to respect the temporal
  discipline of algebraic operations.

- A _graded monads-based modal effect system_ (with added temporal awareness)
  that modularly tracks the effects and resource usage, parameterised over a
  **grade system**: a pair of partially ordered monoids (one for effect
  grades, one for resource grades) together with a grade morphism between them.

The formalisation is developed and tested with Agda version 2.8.0 and Agda
Standard Library version 2.3. To check the whole development, run `make` (which
invokes `agda Everything.agda`); `Everything.agda` imports every module.

## Structure of the formalisation

The syntax and semantics are parameterised over a `LanguageSpec`, which bundles 
the three pieces of data that a concrete instance of the language is built over: 
a grade system, a signature of base types, and operations' signatures.

### Utilities

- `Util/Equality.agda` collects equality-related auxiliary proofs and postulates
  function extensionality — the development's only postulate.
- `Util/Monad.agda` defines monads, used in the top-level operational semantics.

### Grades and grade systems

- `Syntax/Grades.agda` defines the notion of a `Grade` (a partially ordered
  monoid with an inclusion of ℕ as "so many time steps"), grade morphisms
  `_→ᵍ_`, and a `GradeSystem` (effect grades `EGrade`, resource grades
  `RGrade`, and a grade morphism `∣_∣ᵉ` from the former to the latter),
  together with a convenience interface `GradeSystemInterface`.

- A `Grade` also carries **binary joins** and **antisymmetry**: a least upper
  bound `_⊔_`, the one direction of distributivity that monotonicity does not
  already give, `ρ · (σ ⊔ τ) ≾ (ρ · σ) ⊔ (ρ · τ)` and its mirror, and
  `≾-antisym`. Since the order is a partial one, the derived laws are
  *equations*: the other direction of each distributivity, and the join's
  idempotence, commutativity, associativity and its law against the greatest
  grade, all hold at `_≡_`. A grade morphism preserves joins on the nose. A
  branching construct is graded by the join of its branches, and type
  inference reports the join of two bounds.

- A `Grade` also carries the data type inference reads: a **decidable** order
  (`_≾?_`), hence, by antisymmetry, decidable equality; and two optional
  declared properties, whether the unit is least (`u-least?`) and whether
  `_·_` is commutative (`·-comm?`), which the open calculus's `minᵣ`/`minₑ`
  and `≡̂ᵣ-comm`/`≡̂ₑ-comm` take as `Is-just` proofs and the solver reads
  directly.

- `Syntax/Grades/Example.agda` indexes the example grades, which come in two
  families, and the grade systems assembled from them.

- `Syntax/Grades/Example/Time/` holds the grades that measure only elapsed
  time: `LeftSided` ("at least `n` steps"), `RightSided` ("at most `n`"),
  `TwoSided` (a window `[ min , max ]`), and `TwoSidedWithInfinity`, whose
  upper endpoint may be `∞` (its extended-natural arithmetic is in
  `ExtendedNat.agda`).

- `Syntax/Grades/Example/Traces/` holds the grades that record *which runs* a
  computation may have had, as non-empty finite sets of timed traces. Every
  carrier is canonical — its lists are sorted strictly increasingly for the
  order on traces, hence duplicate-free — so a set has one representation and
  the union of two grades is their join. `Subsets/RightSided.agda` compares
  sets outright, by inclusion. The lifted grades compare closures instead —
  upward for a floor, downward for a cap — so their carrier is cut down
  further, to the **antichain** of a set's minimal members for the order
  (`Syntax/Grades/Traces/Reduced.agda`): a grade names exactly what the
  closure determines, so at a floor `⟅ ε ⟆` and `⟅ ε ∣ ⌈ o ⌉ ⟆` are the same
  grade, the dominated member dropping out. Every order here is therefore a
  partial order: mutually-weakening grades are equal.
  `Lifted/{LeftSided,RightSided,TwoSided}.agda` are the constructions,
  parameterised by an order on traces; `Timed/*` instantiate them at the two
  cost-sensitive orders below — a floor, a cap, and their pairing under a
  coherence field — and `Subsets/RightSided.agda` is the cap at equality.

- `Syntax/Grades/Traces.agda` indexes the shared timed-trace toolkit these are
  built on: `Positive` (the strictly positive duration a delay carries), `Base`
  (timed traces and their sequencing monoid), `Lexicographic` (a strict total
  order on traces, over one on the alphabet, which is what makes the carrier
  canonical), `Sets` (sorted duplicate-free non-empty finite sets of traces,
  the language product, their union, and subset inclusion), `Restriction`
  (restriction along a sub-alphabet), `Durations` with `MaxDuration` and
  `MinDuration` (worst- and best-case aggregation over a set), and
  `Order`/`Reduced` (the interface a trace order supplies, in two layers — the
  order-theoretic half `TracePartialOrder`, which the converse `flipᵖ` meets
  as well, and the two unit facts `TraceOrder` adds on top — together with the
  antichains of the order's minimal members that the lifted grades take as
  their carrier, floors at the order and caps at its converse; stated once, so
  each order below meets the interface once and inherits the whole
  construction with its laws).

- The two cost-sensitive orders on traces live in `Syntax/Grades/Traces/Allowance/`
  and `Syntax/Grades/Traces/Coverage/`. Both are parameterised by a cost model
  `cost : Op → ℕ` and both induct on a running number of time units,
  whose arithmetic is shared in `Slack.agda`; each has `Core`, `Moves`,
  `Decidable` and `Duration` submodules, with `Antisym.agda` proving the order
  antisymmetric and `AsOrder.agda` packaging it as a `TraceOrder`. The
  allowance order asks in addition that every operation cost something, and
  `Allowance/ZeroCost.agda` is the checked negative that makes the hypothesis
  necessary: at a free operation the empty bound permits a run different from
  itself, so neither antisymmetry nor the unit fact `≼-ε-inv` survives.

- Under the **allowance** order `_≼ᵃ_` a bound's operations are permissions and
  its delays are a budget, which the run spends on idling and on operations the
  bound does not name, at their execution time. So `⌈ o ⌉ ≼ᵃ ⟨ n ⟩` exactly when
  `cost o ≤ n`, and never the other way round: a permitted operation buys no
  time. Budget does not cross an operation the bound names, so a bound says
  *when* its slack is available and not merely how much of it there is.

- Under the **coverage** order `_≼ᶜ_` a run covers a guarantee when every
  operation the guarantee names genuinely occurs in it, in order, and every
  delay it names is met by what the run does between the same two named
  operations. So doing more than was asked still covers, and time never buys an
  operation — idling does not discharge "a reading was taken".

- The two are incomparable, and deliberately so: this is why a two-sided trace
  grade takes one order at each endpoint. An allowance wants a listed delay to
  buy the run's operations; a guarantee read the same way would let a run that
  merely idles discharge a demand for a reading. `Traces/Prefix.agda` records
  the other side of this: a contiguity-demanding order carries no grade at all,
  with a checked proof that the language product is not monotone for it.

- `Syntax/Grades/Example/System/` assembles full grade systems, pairing an
  effect grade with a resource grade along a projection saying what the
  resource grade may forget. `Identity.agda` forgets nothing — one grade read
  as both components, so that `mapᵉ` drops out of the typing rules.
  `IntervalsToLeftSidedIntervals.agda` keeps a two-sided interval's lower
  endpoint, discarding the deadline. `Traces/Timed/*` and
  `Traces/Subsets/RightSided.agda` measure a set of traces by a duration: the
  sets are read disjunctively, so a cap has to cover its slowest listed run
  and a floor may promise only its fastest.

- `Syntax/Grades/Example/Worked/` instantiates all of the above at one fixed
  alphabet — a sensor node that can `read` (1 tick), `write` (2–3) and `send`
  (4–6) — and exhibits as checked Agda terms which orderings hold between
  concrete grades and what each morphism does to them: `Operations.agda` fixes
  the alphabet and its runs, `Time.agda` and `Traces/*` work out the orderings
  one grade at a time, `Spec.agda` gives a language specification over it, and
  `Systems.agda` computes the projections. Positive and negative claims are
  both discharged by *running* the relevant decision procedure, so a table
  asserted the wrong way round does not typecheck.

- `Syntax/Grades/Example/Worked/Typing/` then fixes a language over that
  alphabet and types example computations against these grades, exercising
  operations, sequencing, `delay`, `if`, pattern matching, functions,
  `box`/`unbox` and effect handlers. Each of the seven instances (three time
  grades and all four trace grades, each over its identity grade system) writes
  its programs out in full at its own grades, discharging every side condition
  a rule imposes — `var`'s bound, `unbox`'s premise, `coerce`'s ordering — at
  the point it imposes it, by running the grade's own decision procedure; where
  a grade refuses a program, a refutation of the bound it would have needed
  stands in its place. So what a grade lets a program do, and what it refuses,
  is settled by whether the program typechecks.
  `Typing/Core.agda` holds what
  the programs are written *with*: the language itself, the three ways of
  meeting `var`'s bound, and the operation clauses handed to `handle`. The
  index module `Typing.agda` tabulates how the instances differ: what a box
  means at each grade, whether an ordinary variable goes stale, and whether a
  handler clause may drop its continuation. It also records how sub-effecting
  meets the modality — sequencing locks its continuation by the grade its first
  part is *typed at*, so coercing that part changes what the continuation may
  unbox, and only ever for the worse (`coercion-only-closes`).

### Core language, type system

- `Syntax/BaseTypes.agda` defines the signature of base types (with decidable
  equality, eternal base types, and constants).
- `Syntax/GroundTypes.agda` defines ground types (used as operation parameter
  and arity types), including the temporal modality `[ ρ ]ᵍ A` on ground types.
- `Syntax/Operations.agda` defines operation signatures, including each
  operation's parameter and arity ground types and its (maximal) execution grade.
- `Syntax/Types.agda` defines value and computation types.
- `Syntax/Contexts.agda` defines variables and structured contexts, including
  the time-passage context former `Γ ⟨ ρ ⟩`.
- `Syntax/Subtyping.agda` defines shape-preserving subtyping of value and
  computation types, `_<:ᵛ_` and `_<:ᶜ_`, in which a function's domain and a
  box's grade are contravariant and a computation's effect covariant. It is a
  partial order on types: antisymmetry of the grade orders settles the grade
  positions, so mutually-subtyped types are equal. It also
  defines least upper bounds of types, `_⊔ᵛ_≡_` and `_⊔ᶜ_≡_`, as inductive
  relations in the same style. They are partial, and deliberately: the
  contravariant positions are pinned to a shared domain and a shared grade,
  because joining them would ask for *meets* of value types and of resource
  grades, which the grades do not have. The only component genuinely joined is
  a computation's effect, where `_⊔ₑ_` always exists.
- `Syntax/Language.agda` defines well-typed values and computations.
- `Syntax/Renamings/` defines context renamings: `Base.agda` the generating
  calculus (eternal contexts and the `Ren` datatype, indexed by an *ambient*
  context it must fix), `Equivalence.agda` when two renamings act alike
  (`_≐ʳ_`), `Coherence.agda` the laws of the action with respect to it, and
  `Category.agda` the categorical structure this all amounts to.
- `Syntax/RenActions.agda` defines renamings' action on well-typed terms.
- `Syntax/Terms/Equivalence.agda` records that equality of terms is
  propositional equality — the data a term stores that no rule inspects (a
  `var`'s and an `unbox`'s grade bounds, a `coerce`'s ordering) is
  proof-irrelevant — so the congruences are `cong`/`cong₂` and only the three
  irrelevance laws and `handle-≡` are named. `Syntax/Terms/Transport.agda`
  retypes a term along an equality of contexts.
- `Syntax/Substitutions/` defines parallel substitutions and their metatheory:
  `Base.agda` the substitutions themselves, `Lookup.agda` what one does to a
  variable, `Action.agda` its action on terms, `Equivalence.agda` when two act
  alike, `Chain.agda` and `ChainEquivalence.agda` their composition,
  `Interchange.agda` that renaming and substitution commute, `Laws.agda` the
  resulting laws, and `Subsumption.agda` subsumption for contexts (a
  computation over a binder of `A` is one over any subtype of `A`).
  `Variables.agda`, `At.agda` and `Clauses.agda` then specialise all of this to
  substituting at a context's prefix boundary, which is the form every consumer
  uses; `Syntax/Substitutions.agda` re-exports that, with replacing a single
  variable as notation over it.
- `Syntax/CompContext.agda` defines computation term and evaluation contexts.

### Operational semantics, progress and preservation theorems

- `OperationalSemantics/State.agda` defines the states of the stateful,
  temporally-aware operational semantics and auxiliary results about them.
- `OperationalSemantics/PreservationTheorem.agda` defines the small-step
  reduction relation on well-typed computations; as the semantics is defined on
  well-typed computations, it simultaneously proves the preservation theorem.
- `OperationalSemantics/ProgressTheorem.agda` proves the progress theorem.
- `OperationalSemantics/TopLevelOpSemantics.agda`,
  `TopLevelPreservationTheorem.agda`, and `TopLevelProgressTheorem.agda` give a
  top-level operational semantics (interpreting unhandled algebraic operations) 
  together with the corresponding preservation and progress theorems.

### Equational theory

- `EquationalTheory/EquationalTheory.agda` defines an equational theory for the
  language inspired by the standard equational presentations of local state.
- `EquationalTheory/Alignment.agda` shows that the syntactic equivalence of
  terms is contained in the equational theory.

### Denotational semantics

- `DenotationalSemantics/Model/` gives an abstract model interface, which the
  interpretation is parameterised over: `Category.agda` the ambient category,
  `World.agda` the Kripke frame of worlds (a single family of preorders
  `_⊑[ ρ ]_` graded by the resource grades — the frame itself carries no monoid
  structure), `Modality/{Future,Past,Adjunction,Eternal}.agda` the box and
  context modalities and the adjunction between them, `GroundTypes.agda` and
  `GroundEternal.agda` the interpretation of ground types,
  `Monad.agda` a graded monad with algebraic operations and handling, which
  folds a handler into an algebra (with `Monad/Enrichment.agda` relating its
  strength to an enrichment), `TickMonad.agda` the monad the top-level machine
  runs in, and `Implementation.agda` bundling it all.
- `DenotationalSemantics/Model/Example/PSh/` is a concrete model on
  setoid-valued presheaves over the worlds: `Base.agda` the category,
  `Modality/*` the modalities, `Monad/*` the effect-tree monad with its
  handling and its laws, and `TickMonad.agda`, `Implementation.agda`,
  `TopLevelInstance.agda` the instances.
- `DenotationalSemantics/Model/Example/World/` gives concrete Kripke frames,
  one per example grade and in two families: `Ticks/*`, whose worlds are
  elapsed time, and `TraceHistory/*`, whose worlds are the run so far.
- `DenotationalSemantics/Interpretation/` interprets the language in any such
  model — `Types.agda`, `Contexts.agda`, `Variables.agda`, `Terms.agda` — and
  proves the interpretation coherent with the syntactic structural operations:
  `Renaming/` and `RenamingCoherence.agda` for renamings,
  `SubstitutionCoherence/` for substitutions. `State.agda` interprets the
  states of the operational semantics.

### Soundness and adequacy

- `EquationalTheory/Soundness.agda` (with `Soundness/`) proves the equational
  theory sound for the denotational semantics: every derivable equation
  `M == N` denotes an equality of morphisms `⟦M⟧ ≈ᵐ ⟦N⟧`.
- `OperationalSemantics/Soundness/Preservation.agda` (with `Preservation/`)
  proves the small-step semantics sound: a step relates denotationally equal
  configurations, a configuration `⟨ S , M ⟩` interpreting as `M` with its
  context plugged by the state. `Soundness/TopLevelPure.agda` does the same for
  the pure top-level machine.
- `OperationalSemantics/Adequacy/` proves the converse direction: two programs
  with equal denotations halt with the same shape, at the same operation, and
  with the same answer. It is assembled from `Normalization.agda` (a weak head
  normal form exists), the soundness above, and head faithfulness
  (`HeadFaithful.agda` abstractly, `PSh/*` for the presheaf model), over the
  logical relation in `Reducibility.agda` and `Environment/`.
  `Adequacy/Equational.agda` reads this back for the equational theory:
  reasoning in it is observationally valid.

### Type inference

Inference for the open calculus, by constraint generation and solving.

- `TypeInference/Scopes.agda` gives scopes of unknowns: one counter each for
  type, resource-grade and effect-grade variables, so that every scope
  extension reduces definitionally.

- `TypeInference/OpenSyntax/` is the open calculus. `Grades.agda` has open
  grade expressions — a variable, an embedded closed grade, a product, a binary
  join, and (on the resource side) the image of an effect expression under
  `mapᵉ`; `Types.agda` and `Contexts.agda` the open types and contexts, with
  `ContextsLemmas.agda` for lookup under weakening and substitution;
  `Subst.agda` substitutions between scopes. `Hyps.agda` has hypothesis sets
  and entailment: convertibility `_≡̂_`, entailed ordering `_⊩_≾̂_`,
  eternality, the var-rule disjunction `VarOK`, and shape-preserving subtyping
  of open types. `Language.agda` is the qualified judgement `Q ∣ Γ ⊢C⦂ C`: the
  rules of `Syntax/Language.agda` over open types, their side conditions
  entailed from `Q`, with `handle` typing its operation clauses at a rigid
  effect variable, and three rules recording a type annotation.

- `TypeInference/Raw/Syntax.agda` defines raw terms, untyped and scoped by the
  grade and type variables of the context; `box` carries its grade, an
  expression over that scope. Optional type annotations — of a value
  (`V ⦂ᵛ A`), a computation (`M ⦂ᶜ C`) and a lambda's argument
  (`lam[ A ] M`) — are open types over that scope: they fix a shape, and
  generation checks the term against them. `Raw/Subst.agda` substitutes into
  the annotations. `TypeInference/Erase.agda` erases a derivation to a raw term.

- `TypeInference/Constraints/` is the constraint language — type equations,
  value-type subtyping, grade orderings, eternality, the var-rule disjunction,
  `∃` over the three sorts, a rigid `∀ᵉ`, and a conjunction over operations —
  with satisfaction `σ ⊨[ Q ∣ R ] C` relative to hypotheses `Q` and
  obligations `R`.

- `TypeInference/Generate.agda` generates a constraint from a raw term and an
  expected type, an upper bound. It is sound (`Soundness.agda`: a solution
  elaborates to a derivation erasing to the term) and complete
  (`Completeness.agda`: a derivation satisfies the constraint generated from
  its erasure).

- `TypeInference/Solver.agda` axiomatises a solver. Its outcome
  (`Outcome.agda`) is solved, refuted or stuck. A solution `(σ , Q , R)`
  solves the constraint (`solve-sound`) and is principal at each closed
  instance (`solve-principal`); a refutation leaves no solution under
  satisfiable conditions (`solve-refutes`). Nothing is claimed of stuck.

- `TypeInference/Principality.agda`: `PrincipalTyping Γ M` is a scheme
  `∀ Θ̃. Q̃ ∧ R̃ ⇒ X̃` whose every instance types `M` (`instantiate`) and
  through which every typing of `M` factors at each closed instance
  (`factor`). `Typable Γ M` is a typing under satisfiable hypotheses;
  `typable-⇔` gives `Typable Γ M ⇔ Satisfiable Q̃ R̃`. `Inference Γ M` is
  `typed`, `untypable` or `stuck`.

- `TypeInference/OpenSyntax/Instances.agda` gives the models: closed instances
  `δ : Subst Θ ∅ˢ`. Satisfaction `δ ⊨ Q ∣ R` is derivability from no
  hypotheses at `δ`, each clause's rigid kept a parameter; an obligation
  `∀ᵉ j₁ … jₖ. Q` holds when `Q` is derivable at fresh rigids. `Satisfiable`
  and semantic entailment `_⊨ᴴ_` are stated through it. The key lemma
  (`val-≾ᵣ`, `val-≾ᵣ⁻` and their companions): at closed expressions, entailed
  ordering is the carrier's ordering of values and convertibility is equality
  of values. Closed subtyping, eternality and `VarOK` are decidable.

- `TypeInference/SolverImpl.agda` is the concrete solver (`solver : Solver`),
  over an enumeration of the operations (`SolverImpl/Enum.agda`), with its
  report and inference. `SolverImpl/`:
  - `Solve.agda`: the driver. Type equations go to unification, subtyping is
    decomposed, other atoms are residualised; at the close of a rigid scope
    the atoms are kept, discharged or deferred.
  - `Localise.agda`: principal values for the unknowns local to a rigid scope.
  - `Deferred.agda`: deferred rigid conditions `∀ᵉ j₁ … jₖ. O`, retried after
    each close and read back as obligations.
  - `Principal.agda`: principality and refutation for the driver.
  - `Closed.agda`: atoms with no unknowns, decided by the grade's `_≾?_`.
  - `Product.agda`, `Normal.agda`, `Canon.agda`: the sum-of-products normal
    form, its products sorted at commutative grades; deciding entailed
    ordering (`decide≾ᵣ`/`decide≾ₑ`); the canonical form of reported grades.
  - `Simplify.agda`: settles disjunctions and prunes entailed atoms of a
    report.
  - `Eliminate.agda`: Pottier's elimination of unknowns (ICFP 1996), and
    replacement of an unknown by an expression the hypotheses equate it with.
  - `Strengthen.agda`: a report over the variables occurring in it; `Vars.agda`
    sets of variables.
  - `Refute.agda`: refutation of an ordering against the unit.
  - `Resid.agda`, `State.agda`, `Polarity.agda`: residual constraints, the
    solver state, the polarity of an unknown.
  - `Expand.agda`: skeleton expansion of type unknowns.
  - `Core/`: McBride-style first-order unification of types and of skeletons,
    sound and most general, never binding a rigid.

- The end-to-end theorem (`SolverImpl.agda`): `infer Γ M : Inference Γ M`;
  `infer-typed` — a `typed p` verdict has `Typable Γ M ⇔ Satisfiable Q̃ R̃`;
  `infer-untypable` — an `untypable` verdict means `¬ Typable Γ M`;
  `infer-complete` — a typable term is never `untypable`.

- The solver reads `u-least?` and `·-comm?` from the grade system.

- `stuck` arises only where a clause's scope closes with a local unknown for
  which `Localise` finds no value. Known cases: a local cycle between the
  clause's rigid and something mentioning it; an outer clause's local on both
  sides of an inner clause's deferred condition; a clause-local under several
  incomparable upper bounds.

- `TypeInference/Examples/` runs inference on nine functions of the
  prototype's standard library. `Stdlib.agda` proves, over an arbitrary
  language, that inference answers `typed` for each; `Stdlib/` checks the
  reported scheme by `refl` at four grades, covering `u-least?` and `·-comm?`.
  `Report.agda` writes schemes as `∀[ a , b , c ] C ⟹ X`.
  `Annotations.agda` gives one program per annotation form with the type it
  forces, and `relay`, a typable handler whose clause resumes through the
  identity applied to itself: inference is stuck on it at the four grades,
  and types it once the identity's argument is annotated (`Annotations/`).
