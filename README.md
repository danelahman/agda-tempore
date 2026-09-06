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
  computation had, as non-empty finite sets of timed traces, and its module
  names mirror `Interval/` one for one. `LeftSided.agda` reads a grade as a
  *floor* under what must have happened and `RightSided.agda` as a *cap* on
  what may have; `TwoSided.agda` pairs the two, its carrier a pair of sets with
  a consistency field `lo≼hi` playing the role of `min≤max`. `Inclusion.agda`
  is the odd one out — it compares sets by membership alone, so it is not an
  interval in either direction — and `Convex.agda` is the Egli-Milner lift,
  which despite the name is *not* a two-sided interval and never caps a run
  from above. The two lifts to sets of traces are in
  `Syntax/Grades/Traces/SubtraceLift.agda`: the floor takes the Smyth one and
  the cap the Hoare one, mirroring `min i₂ ≤ min i₁` against `max i₁ ≤ max i₂`.

- The orders all run the way `unbox`'s premise `ρ' ≾ᵣ ρ` needs, with `ρ'` the
  effects that actually elapsed and `ρ` the grade on the box. `s ≼ t` reads
  "the run `t` does at least what `s` asks for": every operation `s` names must
  genuinely occur in `t`, while every delay it names is paid out of the time
  `t` spent, operations included at their execution time. So having done more
  than the box asks for still opens it, having done less never does, elapsed
  time discharges a demand for time — and nothing but the operation itself
  discharges a demand for an operation.

- `Syntax/Grades/Traces.agda` indexes the shared timed-trace toolkit these are
  built on: `Positive` (the strictly positive durations a delay carries),
  `Base` (timed traces and their sequencing monoid), `Sets` (non-empty finite
  sets of traces and the language product), `Restriction`, and the
  duration/sub-trace machinery below.

- The *cost-aware* trace-based grades read a set of timed traces against the
  operations' prescribed execution times, given by a map `cost : Op → ℕ`. The
  sub-trace preorder `Syntax/Grades/Traces/Subtrace/` is parameterised by
  that map: an unmatched operation of the *elapsed* run banks `cost o` units of
  slack (`pay-op`) alongside its delays (`del-delay`), and a demanded delay is
  paid out of that slack (`use-delay`). So `⟨ n ⟩ ≼ ⌈ o ⌉` exactly when
  `cost o ≥ n`. There is no rule spending slack on a demanded *operation*, so
  the converse fails: `⌈ o ⌉ ≼ ⟨ n ⟩` never holds (`op-⋠` in
  `Subtrace/Moves.agda`). The preorder itself and its
  reflexivity/weakening/transitivity are in `Subtrace/Core.agda`, the moves
  building sub-trace proofs in `Subtrace/Moves.agda`, and the decision
  procedure in `Subtrace/Decidable.agda`. `SubtraceDuration.agda` proves the
  bound against a demanded pure delay exact — `⟨ n ⟩ ≼[ k ] t` holds precisely
  when `n ≤ duration t + k` — and `SubtraceCost.agda` that *raising* the cost
  widens the order, since a dearer operation banks more time.

- `Syntax/Grades/Example/System/` assembles full example grade systems and
  grade morphisms between their effect and resource grades:
  `IntervalsToLeftSidedIntervals`, `TracesToRestrictedTraces` (sets of
  traces over all operations to sets of traces over a sub-alphabet),
  `TracesToTimeIntervals` (sets of traces to two-sided time intervals), and
  `TracesToCostAwareTraces` (sets of traces ordered by inclusion to the same
  sets ordered up to the cost-aware sub-trace preorder, and one cost model to
  a dearer one), and `TraceIntervalsToTraceSets` (two-sided trace intervals
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
