# The core calculus of Tempore, in Agda

An Agda formalisation of the core calculus of Tempore, a language for
programming with temporal resources: resources that become available only
after some time, some events, or similar has elapsed since they were brought
into scope. The calculus has Fitch-style graded modal types over a grade system
(a grade algebra for effects, one for resources, and a morphism between them),
algebraic effects and handlers whose operations take time, and a graded effect
system. The development has two calculi. The polymorphic calculus has type
and grade variables and quantified type schemes; for it the development gives
constraint-based type inference with principal type schemes, and proves that
its typings instantiate to scope-closed typings, which are type safe and
terminating for a reduction on raw terms. No type of the monomorphic calculus
contains a variable or a quantifier; for it the development proves type safety
and termination, and gives a denotational semantics, a sound equational theory
and adequacy.

The development builds on two earlier formalisations, in which the passage of
discrete time is the only means of specifying temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources)
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).

## Checking

Agda 2.8.0 with the Agda standard library 2.3, registered as
`standard-library-2.3` (see `graded-temporal-resources.agda-lib`).

The two calculi do not import each other; both build on `Grades/`,
`Language/` and `Util/`. There are three roots, with approximate cold build
times on an unloaded machine:

    agda Everything.agda                      # polymorphic calculus, ~30 min
    agda Examples.agda                        # inference examples, ~10 min more
    agda MonomorphicCalculus/Everything.agda  # monomorphic calculus, ~10 min

A set of examples is checked alone by its index,
`agda PolymorphicCalculus/Examples/<Set>/All.agda`, whose header names the
parts of the solver it exercises. A check passes when Agda exits with 0 and
prints no warning. The only postulate is function extensionality
(`Util/Equality.agda`).

## Layout

- `Util/`: equality and the non-negative rationals.
- `Grades/`: grade algebras, grade systems and durations, and the hints the
  solver reads (`Grades/Hints.agda`); the concrete grades in `Grades/Examples/`.
- `Language/`: what both calculi share: base types, ground types,
  comparisons and operation signatures.
- `PolymorphicCalculus/`: the polymorphic calculus: hypotheses, entailment,
  typing, the operational semantics, type safety and termination,
  constraints, the solver, inference.
- `MonomorphicCalculus/`: the monomorphic, intrinsically typed calculus: its
  operational and denotational semantics, equational theory and adequacy.

`Results.agda` and `MonomorphicCalculus/Results.agda` are the overviews: one
entry per main definition, rule and theorem, named by its title; the
monomorphic one lists the items not yet formalised at the end.

## Scope

- Handlers are values of handler types, used by `handle M with V`, in the
  polymorphic calculus; the monomorphic calculus has second-class handlers,
  `handle M with H to x in N`. The language is parameterised by base types, the
  calculus being its instance without them (`withoutBaseTypes`).
- Hypotheses include quantified orderings, which bind several rigid
  effect-grade variables.
- Unbox takes a resource value, a variable under annotations, and binds its
  payload; the monomorphic calculus's unbox takes a variable.
- A top-level definition is named by its position in the program context.
  Inference is for values in program contexts, and for computations in open
  contexts.
- The reduction is on run-time terms, raw terms without grades and type
  annotations, with grade-free states; `unbox` there takes a value.
  Instantiation, type safety and termination are for the scope-closed typing.
  The monomorphic calculus types handler clauses at every continuation grade
  and has comparisons as computations. Completeness of inference is with
  respect to scope-closed typings.
- The denotational results assume uniform handlers, and some of their
  recursions are marked `TERMINATING`.

## Licence

MIT, see `LICENSE.md`.
