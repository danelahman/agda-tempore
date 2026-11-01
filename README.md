# Agda formalisation of the core calculus for grades temporal resources

An Agda formalisation of the core calculus of
[Tempore](https://tempore-lang.ee/), a prototype language for type-safe
programming with temporal resources: resources that become available only after
some time, some events, etc has elapsed since they were brought into scope. The
calculus has Fitch-style graded modal types over a grade system (a grade algebra
for effects, one for resources, and a morphism between them), algebraic effects
and handlers whose operations take time, and a graded effect system.

The formalisation includes two calculi.

- The polymorphic calculus has type and grade variables and quantified type
  schemes. The development gives constraint-based type and grade inference with
  principal type schemes for it, and proves that its typings instantiate to
  scope-closed typings, which are type safe and terminating for reducing.
- The monomorphic calculus has types that do not contain variables or
  quantifiers. The development proves type safety and termination for it, and
  gives a denotational semantics, a sound equational theory and adequacy.

The development builds on two earlier formalisations, in which the passage of
discrete time is the only means of specifying temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources)
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).

## Checking

Agda 2.8.0 with the Agda standard library 2.3, registered as
`standard-library-2.3` (see `graded-temporal-resources.agda-lib`).

The two calculi do not import each other. Both build on `Grades/`, `Language/`
and `Util/`. `Everything.agda` checks every module. Each calculus also has its
own `Everything.agda` root. Approximate timings for typechecking in Agda:

    agda Everything.agda                          # everything, ~22 min
    agda PolymorphicCalculus/Everything.agda      # polymorphic calculus, ~7 min
    agda MonomorphicCalculus/Everything.agda      # monomorphic calculus, ~14 min
    agda PolymorphicCalculus/Examples.agda        # type inference examples, ~6 min more

Each set of type inference examples is checked separately by its index, `agda
PolymorphicCalculus/Examples/<Set>/All.agda`, whose header names the parts of
the solver it exercises. A check passes when Agda exits with 0 and prints no
warning. The only postulate is function extensionality (`Util/Equality.agda`).

The sources use many Unicode symbols, including mathematical letters such as
`𝟏` and `𝕊`, combining accents (`ε̂`) and brackets such as `⦉ ⦊`. A monospace
font with wide coverage, such as [JuliaMono](https://juliamono.netlify.app),
shows them all and keeps columns aligned. DejaVu Sans Mono lacks several.

The root of each calculus, `PolymorphicCalculus/Everything.agda` and
`MonomorphicCalculus/Everything.agda`, names its key modules.

## Layout

- `Util/`: equality and the non-negative rationals.
- `Grades/`: grade algebras, grade systems and durations, the hints the solver
  reads, and the concrete grades in `Grades/Examples/`.
- `Language/`: language specification that both calculi share: base types,
  ground types, comparisons and operation signatures.
- `PolymorphicCalculus/`: syntax, hypotheses and entailment, typing, the
  operational semantics, type safety and termination, constraints, the solver,
  type and grade inference, programs and examples.
- `MonomorphicCalculus/`: the intrinsically typed calculus, its operational and
  denotational semantics, equational theory and adequacy.

## Scope

- The language is parameterised by base types and operation signatures.
- Both calculi have effect handlers and effect handling.
- Type scheme hypotheses include quantified orderings, which bind several rigid
  effect-grade variables (that are introduced by handler operation cases).
- In the polymorphic calculus, `unbox` takes a resource value, a variable under
  annotations, and binds its payload. In the monomorphic calculus just a variable.
- A top-level (let) definition is named by its position in the program context.
  Inference is for values in program contexts and for computations in open
  contexts, and is complete with respect to scope-closed typings.
- The reduction of the polymorphic calculus is on run-time terms paired with
  run-time states, raw terms without grades and type annotations. A state
  records the grade of each passage of time, and boxed up resources.
  Instantiation, type safety, and termination are for the scope-closed typing.
- The monomorphic calculus types handler clauses at every continuation grade
  by using Agda's dependent functions for a meta-level forall quantifier.
- The denotational results assume uniform effect handlers, which impose a 
  parametricity condition on the typings of monomorphic calculus's handlers.

## Licence

MIT, see `LICENSE.md`.
