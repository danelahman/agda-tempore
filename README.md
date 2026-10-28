# Agda formalisation of a generally graded core language for temporal resources

An Agda formalisation of a (Fitch-style) **generally graded, modally typed,
effectful core language for programming with temporal resources**: resources
that become available only after some amount of time, some events, or similar
has elapsed since they were brought into scope. An example is an assembly
operation that must wait for (car) parts to dry after a paint operation, or for
other actions to happen before further operations are executed.

The development builds on two earlier formalisations, in which the passage of
discrete time is the only means of specifying temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources)
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).
The language formalised here is graded by arbitrary partially ordered monoids.
Effects and resources may be graded by *different* monoids, related by a grade
morphism, which reinterprets an effect grade (for example, a trace or an
interval of possible execution costs) as a resource grade (for example, the
amount of time after which a resource becomes available).

The **main features** of the language are:

- Fitch-style _temporally graded modal types_ `[ ρ ]ᵍ A` (on ground types) and
  `[ ρ ] X` (on value types), expressing that a value of type `A` or `X` is
  available once the resource grade `ρ` has elapsed (for example, after at
  most `ρ` time steps or at most `ρ` events).

- _Temporally aware algebraic effects_: the signature of an operation includes
  its effect grade, and its continuation is typed in a context in which that
  grade has elapsed and further temporal resources are accessible.

- _Effect handlers_, also temporally aware, which respect the temporal
  discipline of algebraic operations.

- A _graded-monad-based modal effect system_ that tracks effects and resource
  usage, parameterised by a **grade system**: two partially ordered monoids
  (effect grades and resource grades) together with a grade morphism from the
  former to the latter.

The development is checked with Agda 2.8.0 and the Agda standard library 2.3.
`make` checks `Everything.agda`, which imports the development except the
type-inference examples. `make examples` checks those, which run the solver at
several grades and take minutes; `make examples-<set>` checks one set, and the
Makefile lists the parts of the solver that each set exercises.

## Structure

- `Util/`: equality and function extensionality, the only postulate, and the
  non-negative rationals.
- `Grades/`: durations, grade algebras and grade systems, their constructions,
  and, in `Grades/Examples/`, the concrete grades.
- `Language/`: the language specification shared by both calculi: base types,
  operations, ground types, comparisons, and value and computation types.
- `OpenCalculus/`: the calculus with type and grade variables, its typing
  under hypotheses, and type inference.
- `ClosedCalculus/`: the intrinsically typed calculus, its operational and
  denotational semantics, the equational theory, and adequacy.
- `Bridge/`: what relates the two calculi: instantiation, and soundness and
  completeness of inference for the declarative system.
