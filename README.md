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
  function extensionality.
- `Util/Time.agda` defines time (as natural numbers) and auxiliary lemmas.
- `Util/Monad.agda` defines monads, used in the top-level operational semantics.

### Grades and grade systems

- `Syntax/Grades.agda` defines the notion of a `Grade` (an ordered
  monoid), grade morphisms `_→ᵍ_`, and a `GradeSystem` (effect grades `EGrade`,
  resource grades `RGrade`, and a grade morphism `∣_∣ᵉ` from the former to the
  latter), together with a convenience interface `GradeSystemInterface`.

- `Syntax/Grades/Example.agda` indexes the example grades and grade systems,
  and explains how they relate. They fall into three groups.

- `Syntax/Grades/Example/Interval/` holds the grades that measure only elapsed
  time: `LeftSided` ("at least `n` steps"), `RightSided` ("at most `n`"),
  `TwoSided` (a window `[ min , max ]`), and `TwoSidedWithInfinity`, whose
  upper endpoint may be `∞` (its extended-natural arithmetic is in
  `ExtendedNat.agda`).

- `Syntax/Grades/Example/TraceSet/` holds the grades that record *which runs* a
  computation must have had, as non-empty finite sets of timed traces. The
  first three share their carrier and monoid and differ only in the order:
  `Inclusion.agda` orders sets by inclusion, `UpToSubtrace.agda` by the Smyth
  lift of the sub-trace preorder, and `Convex.agda` by its Egli-Milner lift.
  Despite its name the convex order is *not* a two-sided interval and never
  caps a run from above — both its halves orient `≼` the same way.
  `TwoSided.agda` is the two-sided interval: its carrier is a *pair* of sets,
  a floor and a cap, with a consistency field `lo≼hi` playing the role of
  `min≤max`, so a run must cover a trace of the floor and fit inside a trace
  of the cap. It is the trace analogue of `Interval/TwoSided.agda`, with `≼`
  in place of `≤`.

- All the grade orders run the same way round, which is what `unbox`'s premise
  `ρ' ≾ᵣ ρ` needs: `ρ'` records the effects that actually elapsed since the
  boxed resource came into scope, `ρ` is the grade on the box, and a grade is
  a *lower* bound on what must have happened. So having done more than `ρ` asks
  for still opens the box, and having done less never does — mirroring
  `[ m ,+∞⟩ ≾ [ n ,+∞⟩` iff `n ≤ m` for the left-sided intervals. The two lifts
  of the sub-trace preorder used to build these orders are in
  `Syntax/Grades/Traces/SubtraceLift.agda`.

- `Syntax/Grades/Traces.agda` indexes the shared timed-trace toolkit these are
  built on: `Positive` (the strictly positive durations a delay carries),
  `Base` (timed traces and their sequencing monoid), `Sets` (non-empty finite
  sets of traces and the language product), `Restriction`, and the
  duration/sub-trace machinery below.

- The *cost-aware* trace-based grades read a set of timed traces against the
  operations' prescribed execution times, given by a map `cost : Op → ℕ`. The
  sub-trace preorder `Syntax/Grades/Traces/Subtrace/` is parameterised by
  that map: alongside `use-delay`, spending slack on a leading delay of the
  smaller trace, a `use-op` rule spends slack on a leading *operation*, at the
  time that operation takes. So an operation performed fits inside a pure time
  budget, `⌈ o ⌉ ≼ ⟨ n ⟩` as soon as `cost o ≤ n`. Slack is created only by
  absorbing the *delays* of the larger trace, so the converse fails: a schedule
  calling for an operation is not met by spending the same time on anything
  else (`⟨suc⟩-⋠` in `Subtrace/Moves.agda`) — so a demand for an operation is
  discharged by enough time passing, while a demand for elapsed time is not
  discharged by having spent it on operations. The preorder itself and its
  reflexivity/weakening/transitivity are in `Subtrace/Core.agda`, the moves
  building sub-trace proofs in `Subtrace/Moves.agda`, and the decision
  procedure in `Subtrace/Decidable.agda`. `SubtraceDuration.agda` proves the
  two bounds exact — `s ≼[ k ] ⟨ n ⟩` holds precisely when
  `duration s ≤ n + k` — and `SubtraceCost.agda` that lowering the cost only
  widens the order.

- `Syntax/Grades/Example/System/` assembles full example grade systems and
  grade morphisms between their effect and resource grades:
  `IntervalsToLeftSidedIntervals`, `TracesToRestrictedTraces` (sets of
  traces over all operations to sets of traces over a sub-alphabet),
  `TracesToTimeIntervals` (sets of traces to two-sided time intervals), and
  `TracesToCostAwareTraces` (sets of traces ordered by inclusion to the same
  sets ordered up to the cost-aware sub-trace preorder, and one cost model to
  a cheaper one), and `TraceIntervalsToTraceSets` (two-sided trace intervals
  to one-sided ones, forgetting the cap — the trace counterpart of the first).
  Each projection says what a resource grade is allowed to forget about the
  effect grade it comes from.

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
- `Syntax/Substitutions.agda` defines the action of substituting, and
  `Syntax/Substitutions/` its metatheory: `Variables.agda` how a substitution
  acts on a variable, `Weakening.agda` that substituting for a freshly weakened
  variable is the identity, `Renaming/` that renaming commutes with
  substitution, and `Swap/` that two adjacent prefix substitutions commute.
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

## Work in progress

The equational soundness proof (`EquationalTheory/EquationalSoundness.agda`)
and its formalisation remain currently a work in progress.
