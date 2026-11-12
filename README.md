# Agda formalisation of the core calculus of Tempore

An Agda formalisation of the core calculus of
[Tempore](https://tempore-lang.ee/), a language for type-safe programming with
temporal resources: resources that may be used only while the time, the
events, etc. that have elapsed since they were brought into scope stay within a
prescribed grade, e.g., only after, or only before, some time has passed.
The calculus has Fitch-style graded modal types over a grade system (a grade
algebra for effects, one for resources, and a morphism between them),
effect-graded algebraic effects and effect handlers, and a graded effect system.

The development formalises two calculi:

- **Polymorphic calculus** has type and grade variables, and quantified type
  schemes. The development gives constraint-based type and grade inference with
  principal type schemes for it, and proves that its typings instantiate to
  scope-closed typings, which are type safe, and their reduction terminates.
- **Monomorphic calculus** has types that do not contain variables or
  quantifiers. The development proves type safety and termination for it, and
  gives a denotational semantics, a sound equational theory, and adequacy. This
  is a declarative simply typed non-polymorphic version of the core calculus.

The development builds on two earlier formalisations, in which the passage of
discrete time is the only means of specifying temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources)
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).

## Typechecking in Agda

Agda 2.8.0 with the Agda standard library 2.3, registered as
`standard-library-2.3` (see `graded-temporal-resources.agda-lib`).

The two calculi do not import each other. Both build on `Grades/`, `Language/`,
and `Util/`. `Everything.agda` checks every module, including the type inference
examples. Each calculus also has its own `Everything.agda` root module, which
leaves the type inference examples out. Approximate timings for typechecking in
Agda are

    agda Everything.agda                          # everything, ~27 min
    agda PolymorphicCalculus/Everything.agda      # polymorphic calculus, ~6 min
    agda MonomorphicCalculus/Everything.agda      # monomorphic calculus, ~14 min
    agda PolymorphicCalculus/Examples.agda        # type inference examples, ~11 min

Typechecking needs a lot of memory, and we recommend a machine with at least
16 GB. On an Apple M3 Pro with 18 GB, the peak memory footprint of the
polymorphic calculus and of `Everything.agda` is about 20 GB, of which 10 to
13 GB are resident, and Agda was killed in a container limited to 12 GB.
The monomorphic calculus peaks at about 6.5 GB.

Each set of type inference examples is checked separately by its index, `agda
PolymorphicCalculus/Examples/<Set>/All.agda`, whose header names the parts of
the solver it exercises. A check passes when Agda exits with 0 and prints no
warning. The only postulate is function extensionality (`Util/Equality.agda`).
The denotational semantics and the adequacy proof of the monomorphic calculus
use eight `TERMINATING` pragmas for difficult-to-prove-terminating recursions,
each justified where it stands; the polymorphic calculus uses none.

The sources use many Unicode symbols, including mathematical letters such as
`𝟏` and `𝕊`, combining accents (`ε̂`), and brackets such as `⦉ ⦊`. A monospace
font with wide coverage, such as [JuliaMono](https://juliamono.netlify.app),
shows them all and keeps columns aligned. DejaVu Sans Mono lacks several.

The root of each calculus, `PolymorphicCalculus/Everything.agda` and
`MonomorphicCalculus/Everything.agda`, names its key modules.

## Layout

- `Util/`: equality and the non-negative rationals.
- `Grades/`: grade algebras, grade systems and durations, the constructions on
  grade algebras (products, semidirect products, indexed families, mode
  matrices), timed traces, regular languages and timed regular expressions, the
  hints the solver reads, and the example grade algebras and grade systems,
  indexed in `Grades/Examples.agda`.
- `Language/`: language specification that both calculi share: base types,
  ground types, comparisons, and operation signatures.
- `PolymorphicCalculus/`: syntax, hypotheses and entailment, typing, the
  context modality, the operational semantics, type safety and termination,
  constraints, the solver, type and grade inference, programs, and examples.
- `MonomorphicCalculus/`: the intrinsically typed calculus, its operational and
  denotational semantics, equational theory, adequacy, and examples.

## Notes

- The language is parameterised by base types and graded operation signatures.
- Both calculi support algebraic effect handlers and effect handling.
- Type scheme hypotheses include quantified orderings, which bind several rigid
  effect-grade variables (that are introduced by handler operation cases).
- In the polymorphic calculus, `unbox` takes a resource value, a variable under
  annotations, and binds its payload. The monomorphic `unbox` takes a variable.
- A top-level (`let`) definition is named by its position in the program context.
  Inference is for values in program contexts and for computations in open
  contexts, and is complete with respect to scope-closed typings.
- The reduction of the polymorphic calculus is on run-time terms paired with
  run-time states, raw terms without grades and type annotations. A state
  records the grade of each passage of time, and resources.
  Instantiation, type safety, and termination are for the scope-closed typing.
- The monomorphic calculus types handler clauses at every continuation grade
  by using Agda's dependent functions for a meta-level universal quantifier.
- The denotational results assume uniform effect handlers, which impose a
  parametricity condition on the typings of the monomorphic calculus's handlers.

## Licence

MIT, see `LICENSE.md`.

## AI usage disclaimer

Agentic AI tools (from Anthropic's Claude family) have been used to develop
parts of this formalisation.
