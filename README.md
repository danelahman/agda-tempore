# The core calculus of Tempore, in Agda

An Agda formalisation of the core calculus of Tempore, a language for
programming with temporal resources: resources that become available only
after some time, some events, or similar has elapsed since they were brought
into scope. The calculus has Fitch-style graded modal types over a grade system
(a grade algebra for effects, one for resources, and a morphism between them),
algebraic effects and handlers whose operations take time, and a graded effect
system. For the calculus with type and grade variables the development gives
constraint-based type inference with principal type schemes, and proves that
its typings instantiate to scope-closed typings, which are type safe and
terminating for a reduction on raw terms; for the closed calculus it proves
type safety and termination, and gives a denotational semantics, a sound
equational theory and adequacy.

The development builds on two earlier formalisations, in which the passage of
discrete time is the only means of specifying temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources)
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).

## Checking

Agda 2.8.0 with the Agda standard library 2.3, registered as
`standard-library-2.3` (see `tempore-formalisation.agda-lib`).

    agda Everything.agda    # the development: about 50 minutes from scratch
    agda Examples.agda      # the type-inference examples: about 5 minutes more

A set of examples is checked alone by its index,
`agda OpenCalculus/Examples/<Set>/All.agda`, whose header names the parts of
the solver it exercises. A check passes when Agda exits with 0 and prints no
warning. The only postulate is function extensionality (`Util/Equality.agda`).

## Layout

- `Util/`: equality and the non-negative rationals.
- `Grades/`: grade algebras, grade systems and durations; the concrete grades
  in `Grades/Examples/`.
- `Language/`: what both calculi share: base types, operations, types.
- `OpenCalculus/`: the calculus with type and grade variables: hypotheses,
  entailment, typing, the operational semantics, type safety and termination,
  constraints, the solver, inference.
- `ClosedCalculus/`: the closed, intrinsically typed calculus: its operational
  and denotational semantics, equational theory and adequacy.
- `Bridge/`: instantiation of open typings into closed ones, and completeness
  of inference with respect to closed typings.

`Results.agda` is the overview: one entry per main definition, rule and
theorem, named by its title, with the items not yet formalised listed at the
end.

## Scope

- Handlers are values of handler types, used by `handle M with V`, in the
  calculus with grade variables; the closed calculus has second-class handlers,
  `handle M with H to x in N`. The language is parameterised by base types, the
  calculus being its instance without them (`withoutBaseTypes`).
- Conditions on the variable of a handler clause are kept as obligations of a
  type scheme, apart from its hypotheses.
- Unbox takes a variable.
- Inference is for computations in open contexts; there are no top-level
  programs.
- The reduction is on run-time terms, raw terms without grades and type
  annotations, with grade-free states; `unbox` there takes a value.
  Instantiation, type safety and termination are for the scope-closed typing.
  The closed calculus types handler clauses at every continuation grade and
  has comparisons as computations; the instantiation into it covers the terms
  whose handlers are second class. Completeness of inference is with respect
  to scope-closed typings.
- The denotational results assume uniform handlers, and some of their
  recursions are marked `TERMINATING`.

## Licence

MIT, see `LICENSE.md`.
