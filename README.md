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
ordered monoids to specify effects and verify temporal properties 
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
  **grade system**: a pair of ordered monoids (one for effect grades, one for
  resource grades) together with a grade morphism between them.

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

- `Syntax/Grades.agda` defines the notion of a `Grade` (an ordered monoid with
  an inclusion of ℕ as "so many time steps"), grade morphisms `_→ᵍ_`, and a
  `GradeSystem` (effect grades `EGrade`, resource grades `RGrade`, and a grade
  morphism `∣_∣ᵉ` from the former to the latter), together with a convenience
  interface `GradeSystemInterface`.

- `Syntax/Grades/Example.agda` indexes the example grades, which come in two
  families, and the grade systems assembled from them.

- `Syntax/Grades/Example/Time/` holds the grades that measure only elapsed
  time: `LeftSided` ("at least `n` steps"), `RightSided` ("at most `n`"),
  `TwoSided` (a window `[ min , max ]`), and `TwoSidedWithInfinity`, whose
  upper endpoint may be `∞` (its extended-natural arithmetic is in
  `ExtendedNat.agda`).

- `Syntax/Grades/Example/Traces/` holds the grades that record *which runs* a
  computation may have had, as non-empty finite sets of timed traces. All six
  share the carrier and the monoid of `Syntax/Grades/Traces/Sets.agda` and
  differ only in the order on it. `Lifted/{LeftSided,RightSided,TwoSided}.agda`
  are the constructions, parameterised by an order on traces; `Timed/*`
  instantiate them at the two cost-sensitive orders below and `Subsets/*` at
  equality — each family with a floor, a cap, and their pairing under a
  coherence field.

- Five of the six endpoints are read *disjunctively*, one listed trace carrying
  the grade, so they weaken by gaining members and a union of grades is their
  join — which is what a branching construct wants.
  `Traces/Subsets/LeftSided.agda` is the exception: with equality as the
  comparison the disjunctive floor condition coincides with the cap's, so that
  floor is read conjunctively and weakens by *losing* members instead.

- `Syntax/Grades/Traces.agda` indexes the shared timed-trace toolkit these are
  built on: `Positive` (the strictly positive duration a delay carries), `Base`
  (timed traces and their sequencing monoid), `Sets` (non-empty finite sets of
  traces, the language product, and subset inclusion), `Restriction`
  (restriction along a sub-alphabet), `Durations` with `MaxDuration` and
  `MinDuration` (worst- and best-case aggregation over a set), and
  `Order`/`OrderLift` (the interface a trace order supplies, and its Hoare and
  Smyth lifts to sets — stated once, so each order below meets the interface
  once and inherits both lifts with their laws).

- The two cost-sensitive orders on traces live in `Syntax/Grades/Traces/Allowance/`
  and `Syntax/Grades/Traces/Coverage/`. Both are parameterised by a cost model
  `cost : Op → ℕ` and both induct on a running number of time units,
  whose arithmetic is shared in `Slack.agda`; each has `Core`, `Moves`,
  `Decidable` and `Duration` submodules, with `AsOrder.agda` packaging it as a
  `TraceOrder` and `AllowanceLift`/`CoverageLift` supplying the set-level laws.

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
  endpoint, discarding the deadline. `Traces/Timed/*` and `Traces/Subsets/*`
  measure a set of traces by a duration, each endpoint aggregated in the
  direction it is *read* rather than the direction it bounds.

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
  `box`/`unbox` and effect handlers. Each of the nine instances (three time
  grades and all six trace grades, each over its identity grade system) writes
  its programs out in full at its own grades, discharging every side condition
  a rule imposes — `var`'s bound, `unbox`'s premise, `coerce`'s ordering — at
  the point it imposes it, by running the grade's own decision procedure; where
  a grade refuses a program, a refutation of the bound it would have needed
  stands in its place. So what a grade lets a program do, and what it refuses,
  is settled by whether the program typechecks. `Typing/Core.agda` holds what
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
- `Syntax/Language.agda` defines well-typed values and computations.
- `Syntax/Renamings/` defines context renamings: `Base.agda` the generating
  calculus (eternal contexts and the `Ren` datatype, indexed by an *ambient*
  context it must fix), `Eternal.agda` the eternal restriction's action on them,
  `Equivalence.agda` when two renamings act alike (`_≐ʳ_`), `Coherence.agda` the
  laws of the action with respect to it, and `Category.agda` the categorical
  structure this all amounts to.
- `Syntax/RenActions.agda` defines renamings' action on well-typed terms.
- `Syntax/Terms/Equivalence.agda` defines equality of terms (`_≐ᵛ_`/`_≐ᶜ_`,
  which are propositional equality: the grade bounds a term stores are
  proof-irrelevant) together with a congruence per former, and
  `Syntax/Terms/Transport.agda` retyping a term along an equality of contexts.
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
