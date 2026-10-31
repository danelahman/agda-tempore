# The core calculus of Tempore, in Agda

An Agda formalisation of the core calculus of Tempore, a language for
programming with temporal resources: resources that become available only
after some time, some events, or similar has elapsed since they were brought
into scope. The calculus has Fitch-style graded modal types over a grade
system (a grade algebra for effects, one for resources, and a morphism between
them), algebraic effects and handlers whose operations take time, and a graded
effect system.

There are two calculi.

- The polymorphic calculus has type and grade variables and quantified type
  schemes. The development gives constraint-based type inference with
  principal type schemes for it, and proves that its typings instantiate to
  scope-closed typings, which are type safe and terminating for a reduction on
  raw terms.
- No type of the monomorphic calculus contains a variable or a quantifier. The
  development proves type safety and termination for it, and gives a
  denotational semantics, a sound equational theory and adequacy.

The development builds on two earlier formalisations, in which the passage of
discrete time is the only means of specifying temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources)
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).

## Checking

Agda 2.8.0 with the Agda standard library 2.3, registered as
`standard-library-2.3` (see `graded-temporal-resources.agda-lib`).

The two calculi do not import each other; both build on `Grades/`,
`Language/` and `Util/`. `Everything.agda` checks every module; each
calculus also has its own root. Approximate cold build times on an unloaded
machine:

    agda Everything.agda                          # everything, ~22 min
    agda PolymorphicCalculus/Everything.agda      # polymorphic calculus, ~7 min
    agda MonomorphicCalculus/Everything.agda      # monomorphic calculus, ~14 min
    agda PolymorphicCalculus/Examples.agda        # inference examples, ~6 min more

The inference examples are not in `Everything.agda`. A set of them is
checked alone by its index,
`agda PolymorphicCalculus/Examples/<Set>/All.agda`, whose header names the
parts of the solver it exercises. A check passes when Agda exits with 0 and
prints no warning. The only postulate is function extensionality
(`Util/Equality.agda`).

The root of each calculus, `PolymorphicCalculus/Everything.agda` and
`MonomorphicCalculus/Everything.agda`, names its key modules and main
results.

## Layout

- `Util/`: equality and the non-negative rationals.
- `Grades/`: grade algebras, grade systems and durations, the hints the solver
  reads, and the concrete grades in `Grades/Examples/`.
- `Language/`: what both calculi share: base types, ground types, comparisons
  and operation signatures.
- `PolymorphicCalculus/`: syntax, hypotheses and entailment, typing, the
  operational semantics, type safety and termination, constraints, the solver,
  inference, programs and examples.
- `MonomorphicCalculus/`: the intrinsically typed calculus, its operational and
  denotational semantics, equational theory and adequacy.

## Scope

- The language is parameterised by base types; the calculus without them is
  its instance `withoutBaseTypes`.
- Both calculi have handlers as values of handler types, used by
  `handle M with V`. The monomorphic calculus also writes
  `handle M with H to x in N` for `handle M with handler N H`.
- Hypotheses include quantified orderings, which bind several rigid
  effect-grade variables.
- In the polymorphic calculus `unbox` takes a resource value, a variable under
  annotations, and binds its payload; in the monomorphic calculus it takes a
  variable.
- A definition is named by its position in the program context. Inference is
  for values in program contexts and for computations in open contexts, and is
  complete with respect to scope-closed typings.
- The reduction of the polymorphic calculus is on run-time terms, raw terms
  without grades and type annotations; a state records the grade of each
  passage of time. Instantiation, type safety and termination are for the
  scope-closed typing.
- The monomorphic calculus types handler clauses at every continuation grade
  and has comparisons as computations.
- The denotational results assume uniform handlers, and some of their
  recursions are marked `TERMINATING`.

## Licence

MIT, see `LICENSE.md`.
