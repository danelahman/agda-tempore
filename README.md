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
  grade, all hold at `_≡_`. A grade morphism preserves joins on the nose. This
  is what lets a branching construct be graded by the join of its branches, and
  what lets type inference report the join of two bounds rather than falling
  back on the greatest grade. The order is also **decidable** (`_≾?_`), which
  type inference relies on, and antisymmetry turns that into decidable equality
  of grades.

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
  context it must fix), `Eternal.agda` the eternal restriction's action on them,
  `Equivalence.agda` when two renamings act alike (`_≐ʳ_`), `Coherence.agda` the
  laws of the action with respect to it, and `Category.agda` the categorical
  structure this all amounts to.
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
  `Interchange.agda` that renaming and substitution commute, `Restrict.agda`
  the eternal restriction's action, and `Laws.agda` the resulting laws.
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
  `Monad.agda` a graded monad with algebraic operations and handling (with
  `Monad/Enrichment.agda` relating its strength to an enrichment),
  `HandlerAlgebra.agda` the algebras a handler folds with, `TickMonad.agda` the
  monad the top-level machine runs in, and `Implementation.agda` bundling it
  all.
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

- `TypeInference/Scopes.agda` gives scopes of unknowns: three independent
  counters, one each for type, resource-grade and effect-grade variables, so
  that extending one leaves the others reducing definitionally.

- `TypeInference/OpenSyntax/` is the language with unknowns in it. `Grades.agda`
  has open grade expressions — a variable, an embedded closed grade, a product,
  a binary join, and (on the resource side) the image of an effect expression
  under `mapᵉ`; `Types.agda` and `Contexts.agda` the open types and contexts,
  with the eternal barrier; `Subst.agda` substitutions between scopes.
  `Hyps.agda` carries hypothesis sets and the calculus of open grades, which
  mirrors the `Grade` record: *convertibility* `_≡̂_` (the monoid laws,
  commutativity of the join, distributivity, the arithmetic of constants, the
  grade morphism's laws, and absorption of a join by an upper bound) and
  *entailed ordering* `_⊩_≾̂_` under a hypothesis set (assumed orderings,
  constants, transitivity, monotonicity, the join's bounds, the top, and
  unit-minimality where a grade has it). Absorption's premise is an ordering
  entailed with no hypotheses, so the two are one mutual definition.
  Idempotence, the top's absorption, associativity of the join and
  antisymmetry at the empty hypothesis set are derived, as they are in
  `Syntax/Grades.agda`. The file also carries shape-preserving subtyping of
  open types.
  `Language.agda` is the mirrored qualified type system — the same rules over
  open types and a hypothesis set — and `Grounding.agda` with
  `GroundingTheorem.agda` lands an open judgement back in the original type
  system once its unknowns are instantiated.

- `TypeInference/Raw/Syntax.agda` defines raw terms, which carry no types at
  all, and `TypeInference/Erase.agda` erases a derivation to one.

- `TypeInference/Constraints/` defines what a generated problem is: type
  equations, value-type subtyping, orderings of resource and effect grades,
  eternality of a type, the disjunction the `var` rule leaves behind, and
  binders for fresh and for rigid variables — together with what it means for a
  substitution to satisfy one.

- `TypeInference/Generate.agda` turns a raw term and an expected open type into
  a constraint, structurally and mirroring the rules former by former. The
  expected type is an *upper bound*, not a pin: where two types the generation
  cannot choose between must meet, it is the right-hand side of a subtyping or
  ordering atom, and the slack is passed on to the subterms.

- `TypeInference/Soundness.agda` and `Completeness.agda` are the two halves of
  its correctness: a solution of a generated constraint elaborates to a mirrored
  derivation that erases back to the raw term it came from, and a derivation
  satisfies the constraint generated from its own erasure.

- `TypeInference/Solver.agda` axiomatises a constraint solver — solve, with
  soundness, completeness and a principal-solution factorisation —
  `Principality.agda` derives principal typings relative to one, and
  `Infer.agda` composes generation, solving and grounding into inference.

- `TypeInference/ParamGround/` supplies the parametricity certificates a
  grounded derivation needs for the denotational side, and it is where two
  notions of parametricity meet. The open calculus is parametric
  syntactically: an operation clause is a single derivation, typed at a rigid
  effect variable. The semantics assumes `EffUniformʰ` instead — that a
  handler's clause family commutes with sub-effecting its continuation's
  residual effect. The bridge between them, `GroundUniform.ground-uniform`, is
  an explicit hypothesis; `ParamGround/Uniform.agda` proves it for a covariant
  fragment, which excludes a nested `handle` and keeps the rigid variable out
  of the positions where the model offers no coercion to transport along — a
  `lam`'s or an application's argument type, a `box`'s grade, the continuation
  grade of a `_⨟_`. The source calculus's own clauses are families indexed by
  the residual effect, parametric only by that assumption; the passage from
  them to the open calculus is not proved, and completeness of inference is
  stated for the open calculus. A refinement for the future is to make the
  source calculus's clauses parametric by construction, typed under a grade
  variable in the context as in the prototype implementation
  [danelahman/tempore-lang](https://github.com/danelahman/tempore-lang): the
  semantic assumption would then be a structural fact, at the cost of grade
  variables in the source calculus and in its model.

- `TypeInference/SolverImpl/` is a concrete solver for the generated
  constraints: sound by construction, but heuristic, so it deliberately does not
  meet the interface's completeness field. What it does prove is principality of
  every solution it finds (`solve-principal`), and that a refusal of a
  constraint without rigid binders is a refutation (`solve-fail`, for the
  fragment `NoRig` of `TypeInference/Solver/Fragment.agda`). At a rigid binder a
  refusal need not be one — a satisfiable cycle such as `c · e ≾ e` is declined —
  and what is proved there is that a failed escape check refutes
  (`popᵉ-escape`). `Core/` is McBride-style first-order unification;
  `Expand.agda` expands a type unknown by skeleton unification, so that
  subtyping demands decompose; `Resid.agda` is the residual worklist.

  A rigid binder is what a handler's operation clause generates, since the
  clause must hold for every effect its continuation may have. The rigid
  variable is never instantiated. Before its scope closes, `Localise.agda`
  sends each unknown local to the scope to the least term over it that
  satisfies it — the join of its lower bounds, where it occurs below nothing
  else (Pottier's condition), else its one upper bound, else the unit where the
  unit is least — so a solution is one term, uniform in the rigid variable.
  `Solve.agda` then removes the rigid variable from an ordering it bounds from
  one side only, by monotonicity: at the unit when it sits on the greater side
  and the unit is least, at the top when it sits on the smaller side.

  Two boundaries read an answer out of the solver. `Restricted.agda`'s
  `reportOn` is the open one: it settles the var-rule disjunctions, drops the
  subtyping and eternality hypotheses the others entail and the grade
  orderings that repeat once canonical, eliminates the unknowns its own
  hypotheses fix, and puts every grade in canonical form. `Close.agda` is the
  ground one. It reads every bound through one view — a join on the left split
  into its parts, an ordering that holds whatever the assignment dropped — so
  its answer does not depend on the order of the constraints. It assigns an
  unknown bounded below the **join** of its lower bounds, formed even while
  they are not yet constants and computed once they are, and one bounded only
  above that bound, and defaults by polarity what neither pass settles.
  `Eliminate.agda` is Pottier's simplification of subtyping constraints (ICFP
  1996): an unknown occurring below nowhere else is sent to the join of *all*
  its lower bounds, and they go with it.

  Grade expressions are normalised by `Product.agda` to a **sum of products** —
  alternatives, each a product of atoms, with products distributed over joins —
  certified by a single convertibility derivation. `Normal.agda`'s decider
  compares such sums: every alternative on the left below some alternative on
  the right, a product against a product position by position, a missing
  position standing for the unit and the top absorbing whatever lies below it.
  `Canon.agda` puts a reported grade in canonical form: alternatives are
  grouped by their skeleton of variables, a group varying in a single constant
  slot is folded into one alternative by distributivity, groups are ordered by
  skeleton, and an alternative the decider places below another is dropped by
  lattice absorption. Decisions are taken on the unfolded sum, since folding
  the left side of a comparison would lose matches. The canonical form is
  relative to what the decider proves, and one shape keeps its arrival order:
  a group of alternatives varying in more than one constant slot, which
  neither folds nor can be sorted without an order on constants.

- `TypeInference/SolverImpl/Demo/` runs the solver and checks every answer by
  computation — each example is discharged by `refl`, so what is inferred is
  checked rather than asserted, and a refusal is paired with the side condition
  that fails, decided by the grade's own procedure. `Generic.agda` holds the
  program shapes that make sense over any grade monoid, and the two instances
  supply their own results: `TimeIntervals.agda` over the sensor node's windows,
  `TimedTraces.agda` over its sets of runs. The pair is the clearest statement
  of what a grade choice buys — the same conditional is graded by a window
  spanning both arms at one, and by the union of their runs at the other, where
  a claim on a boxed resource can also be refused for doing the right things in
  the wrong order. Both also check handler clauses — forwarding, unboxing and
  performing are inferred wherever they are typable, and resuming twice is
  refused — and the constraints at a rigid
  binder that the solver settles, together with the satisfiable cycle it
  declines.
