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
type-inference examples. `make examples` checks those
(`agda TypeInference/Examples.agda`), which run the solver at several grades and
take minutes. They are divided into sets by what they test (`Stdlib`,
`Annotations`, `Handlers`, `Boxes`, `Reports`, `Product`, `Stages`,
`Durations`), each with an index `TypeInference/Examples/<Set>/All.agda` and a
target `make examples-<set>`; the Makefile lists the parts of the solver that
each set exercises.

## Structure of the formalisation

The syntax and semantics are parameterised by a `LanguageSpec`, which consists
of a grade system, a signature of base types, and the signatures of the
operations.

### Utilities

- `Util/Equality.agda` collects auxiliary results on equality and postulates
  function extensionality, the only postulate of the development.
- `Util/Monad.agda` defines monads, used in the top-level operational semantics.

### Grades and grade systems

- `Syntax/Durations.agda` defines a `Duration`, the monoid of the durations
  of `delay`, its morphisms `_→ᴰ_`, and `Stepped` durations, isomorphic to
  ℕ; `Syntax/Durations/Nat.agda` gives ℕ as `ℕᴰ`, a duration being a number
  of time steps, and `Syntax/Durations/NonNegativeRational.agda` the
  non-negative rationals as `ℚ≥0ᴰ`, with the inclusion `ℕ→ℚ≥0ᴰ`.
  A `TimeDomain D` adds a decidable total order that the monoid induces, in
  a commutative cancellative monoid; `Syntax/Durations/Monus.agda` derives
  the strict order, truncated subtraction and the extremal operations, and
  `ℕᵀ` and `ℚ≥0ᵀ` are the instances, the latter `Dense`.

- `Syntax/Durations/Intervals.agda` gives the intervals of a time domain:
  ends are cuts `p ∣ ⁻` and `p ∣ ⁺` (just below and just above `p`), so each
  end is open or closed, and the upper end may be `∞`. Intervals are ordered
  by their ends, summed end by end (an end of a sum open when an end summed
  is) and joined by the hull. `Intervals/Dense.agda` relates the ends to the
  durations admitted: the order is sound for containment and the sum admits
  the sums of what its summands admit, and in a dense time domain with a
  positive duration both are exact (`⊆ⁱ-complete`, `⊕-complete`, the
  Minkowski sum).

- `Syntax/Grades.agda` defines a `Grade D` (a preordered monoid with a
  monoid morphism `of-dur` from the durations `D`), grade morphisms
  `GradeMorphism h` along a morphism `h` of durations and `_→ᵍ_` along the
  identity, and a `GradeSystem` (durations `Dur`, effect grades `EGrade`,
  resource grades `RGrade`, a grade morphism `∣_∣ᵉ` from the former to the
  latter, and optionally `reflects-u?`, that `∣ e ∣ ≾ u` gives `e ≾ u`), with
  the interface `GradeSystemInterface`.

- A `Grade` has a greatest element `⊤` and **binary joins** `_⊔_`, over which
  multiplication distributes: the fields state `ρ · (σ ⊔ τ) ≾ (ρ · σ) ⊔ (ρ · τ)`
  and its mirror image, the converse inequalities following from
  monotonicity. Equality of grades is the order's **equivalence**
  `c ≃ d = c ≾ d × d ≾ c`: the monoid laws and the inclusion of durations are
  stated up to it, and so are the derived laws, both distributive laws and
  the idempotence, commutativity and associativity of the join and its
  absorption by `⊤`. A grade morphism preserves the structure up to `_≃_`.
  A grade may declare that `_≃_` implies `_≡_` (`≃⇒≡?`), informationally;
  `PosetGrade` and `StrictMorphism`
  give, through `posetᵍ` and `strictᵍ`, the instances and morphisms whose laws
  hold on the nose. A branching
  construct is graded by the join of its branches, and type inference reports
  the join of two bounds.

- A `Grade` also carries the data read by type inference: a **decidable**
  order (`_≾?_`), and hence a decidable equivalence (`_≃?_`); and two
  optional properties, that the unit is least (`u-least?`) and that `_·_` is
  commutative (`·-comm?`). The open calculus's `minᵣ`/`minₑ` and
  `≡̂ᵣ-comm`/`≡̂ₑ-comm` take `Is-just` proofs of them, and the solver reads them
  directly.

- `Syntax/Grades/Example.agda` indexes the example grades, in the families
  below, and the grade systems built from them.

- `Syntax/Grades/Example/Time/` holds the grades that measure elapsed time
  only: `LeftSided` (at least `n` steps), `RightSided` (at most `n` steps, `n`
  possibly `∞`), and `TwoSidedWithInfinity` (a window `[ min , max ]`, `max`
  possibly `∞`); the extended natural numbers are in `ExtendedNat.agda`.

- `Syntax/Grades/Example/Time/Dense/` gives the same three shapes over the
  non-negative rationals ℚ≥0 (`NonNegativeRational.agda`, with its extension
  by `∞` in `ExtendedRational.agda`): `LeftSided.agda` (`[ q ,+∞⟩`, at least
  `q` units), `RightSided.agda` (`[0, q ]`, at most `q` units, `q` possibly
  `∞`), and `TwoSided.agda`, the intervals of `Time/Intervals.agda` at ℚ≥0:
  each end open or closed, written ISO style (`[ p , a ]`, `] p , a ]`,
  `[ p , a [`, `] p , a [`), the upper possibly `∞`; its closed intervals are
  the sub-grade `TwoSidedClosed.agda` (`closed→strict`). Their durations are
  ℚ≥0 (`ℚ≥0ᴰ` in `Syntax/Durations/NonNegativeRational.agda`), and each
  receives its discrete counterpart by a grade morphism along the inclusion
  `ℕ→ℚ≥0ᴰ`, sending `n` time steps to `n` units of dense time. Over ℕ an open
  end is notation for the adjacent closed one (`] n , a ]` is
  `[ n + 1 , a ]`, in `TwoSidedWithInfinity.agda`).

- `Syntax/Grades/Example/SecurityLevel.agda` turns a decidable bounded
  join-semilattice of levels into a grade: `_·_` and `_⊔_` are both the join,
  the unit is the least level, `⊤` the greatest, and `of-dur` is constantly
  the unit, for any durations. A boxed value may be unboxed only while the level has not risen
  since boxing. `two-point-levels` is `Low < High`; `taint-sets n` is the
  `n`-fold power, read as sets of taint labels over `Fin n`.

- `Syntax/Grades/Product.agda` defines the componentwise product of two
  grades, `_×ᵍ_`, with projections `π₁ᵍ` and `π₂ᵍ`, pairing `⟨_,_⟩ᵍ`, and the
  product of two grade systems `_×ˢ_`. `Syntax/Grades/Example/Product/`
  instantiates it: `LeftSidedTimeLevel.agda` (at least `n` steps, touching
  nothing above `ℓ`: an embargo with a taint check), `RightSidedTimeLevel.agda`
  (at most `n` steps and level `ℓ`: an expiring untainted capability), and
  `RightSidedTimeEnergy.agda` (at most `n` steps and `e` units of energy: a
  drifting calibration). `Syntax/Grades/Example/System/Product/LeftSidedTimeLevel.agda`
  pairs the left-sided time-and-level effect grade with three resource grades:
  both components (timed declassification), time alone along `π₁ᵍ` (an
  embargo), and the level alone along `π₂ᵍ` (a taint check).

- `Syntax/Grades/Example/Traces/` holds the grades that record *which runs* a
  computation may have had, as non-empty finite sets of timed traces. Every
  carrier is canonical: its lists are strictly increasing for the order on
  traces, hence duplicate-free, so each set has one representation and the
  union of two grades is their join. `Subsets/RightSided.agda` compares sets by
  inclusion. The lifted grades compare upward closures (for a floor) or
  downward closures (for a cap), and their carrier is the **antichain** of a
  set's minimal members for the order (`Syntax/Grades/Traces/Reduced.agda`): a
  grade is determined by its closure, so at a floor `⟅ ε ⟆` and
  `⟅ ε ∣ ⌈ o ⌉ ⟆` are the same grade. Every order here is a partial order.
  `Lifted/{LeftSided,RightSided,TwoSided}.agda` are the constructions,
  parameterised by a time domain and an order on traces; `Timed/*` instantiate
  them at the two cost-sensitive orders below (a floor, a cap, and their
  pairing under a coherence field), over whole steps or dense time, and
  `Subsets/RightSided.agda` is the cap at equality, over whole steps.
  `Lifted/Morphism.agda` maps the lifted grades along a map of traces between
  time domains, and `Timed/Morphism.agda` along a morphism of durations;
  `Timed/Dense.agda` reads every whole-step timed grade in dense time.

- `Syntax/Grades/Example/Traces/Regular/` holds the cap at inclusion over
  non-empty *regular* sets of timed traces, a trace being a word over
  `Op ⊎ tick`. Each set is represented by its canonical minimal DFA (Moore
  refinement, states numbered breadth-first), so equal languages are equal
  grades (`Syntax/Grades/Regular.agda` indexes the automata and their proofs).
  The order is inclusion, decided by a search of `L & ~M` that yields a
  shortest counterexample; the product is concatenation, the join union,
  `⊤ = Σ*`, and `of-dur n = tickⁿ`.

- The literals of the regular grade are extended regular expressions (`|`,
  `·`, `*`, `&`, `~`, `Σ`, `tickⁿ`), elaborated to canonical tables with a
  proved denotation; an empty literal is a type error.

- The finite sets of `Subsets/RightSided.agda` embed in the regular grade,
  preserving all of the structure except that no grade morphism exists:
  `any-run` absorbs products and `Σ*` does not (`Traces/Regular/Subsets.agda`).

- `Syntax/Grades/Traces.agda` indexes the timed-trace toolkit on which these
  grades are built. It is parameterised by a time domain (`TimeDomain`), so
  delays are whole steps over `ℕᵀ` or units of dense time over `ℚ≥0ᵀ`. The
  modules are `Positive` (the strictly positive duration of a delay),
  `Base` (timed traces and their sequencing monoid), `Lexicographic` (a strict
  total order on traces, over one on the alphabet, which makes the carrier
  canonical), `Sets` (sorted duplicate-free non-empty finite sets of traces,
  the language product, union and inclusion), `Restriction` (restriction to a
  sub-alphabet), `Durations` with `MaxDuration` and `MinDuration` (worst- and
  best-case aggregation over a set), and `Order`/`Reduced` (the interface of a
  trace order, in two layers: the order-theoretic `TracePartialOrder`, which
  the converse `flipᵖ` also satisfies, and `TraceOrder`, which adds two facts
  about the unit; and the antichains of minimal members that the lifted grades
  take as carrier, floors at the order and caps at its converse). Each order
  below instantiates the interface once and inherits the construction with its
  laws. Across time domains: `Along` maps traces along a morphism of
  durations, delay by delay, `Embedding` carries antichains along such a map,
  and `RunningTimes` gives operations running-time intervals with open or
  closed ends, the costs being their closed hull.

- The two cost-sensitive orders on traces are in
  `Syntax/Grades/Traces/Allowance/` and `Syntax/Grades/Traces/Coverage/`. Both
  are parameterised by a time domain and a cost model `cost : Op → D` and
  proceed by induction with a running duration banked, whose arithmetic is in
  `Slack.agda` over the monus of `Syntax/Durations/Monus.agda`;
  each has `Core`, `Moves`, `Decidable` and `Duration` submodules,
  `Antisym.agda` proving antisymmetry and `AsOrder.agda` giving a
  `TraceOrder`. The allowance order further assumes that every operation has a
  positive cost; `Allowance/ZeroCost.agda` shows the assumption necessary: at
  an operation of cost zero the empty bound permits a run other than itself,
  so antisymmetry and the unit fact `≼-ε-inv` fail.

- Under the **allowance** order `_≼ᵃ_`, the operations of a bound are
  permissions and its delays a budget, which a run spends on idling and on
  operations the bound does not list, at their execution time. Thus
  `⌈ o ⌉ ≼ᵃ ⟨ n ⟩` holds exactly when `cost o ≤ n`, and `⟨ n ⟩ ≼ᵃ ⌈ o ⌉` never
  holds. Budget does not carry across an operation listed in the bound, so a
  bound specifies *when* its slack is available as well as how much there is.

- Under the **coverage** order `_≼ᶜ_`, a run covers a guarantee when every
  operation the guarantee lists occurs in the run, in order, and every delay
  it lists is met by what the run does between the same two listed
  operations. A run doing more than required covers the guarantee, and time
  never covers an operation.

- The two orders are incomparable, and a two-sided trace grade takes one of
  them at each endpoint. `Traces/Prefix.agda` shows that an order demanding
  contiguity carries no grade: the language product is not monotone for it.

- `Syntax/Grades/Example/Counts/` holds the grades that count, per operation
  (or per class of operations, under an `index : Op → Fin n`), how often a
  computation draws on each. `Power.agda` is the generic construction, `n`
  counters each graded pointwise by a fixed `G`. `AtMost.agda` reads a bound as
  a quota: the order is `≤` on each counter, a larger bound is the weaker
  grade, the unit (no operations) is least, and the join is the pointwise
  maximum; boxing at `upto 3` on `send` is a rate limit. `AtLeast.agda` reads a
  bound as a certainty: the order is `≥` on each counter, a smaller bound is
  the weaker grade, the unit (demanding nothing) is greatest, and the join is
  the pointwise minimum. `Extrema.agda` gives the greatest and least value of
  a natural-number measure over a non-empty list, from which both are built.
  `Occurrences.agda` counts the draws of a timed trace on each counter.

- `Syntax/Grades/Example/System/` assembles grade systems, each pairing an
  effect grade with a resource grade along a projection that determines what
  the resource grade forgets. `Identity.agda` forgets nothing: one grade serves
  as both, and `mapᵉ` disappears from the typing rules.
  `IntervalsToLeftSidedIntervals.agda` keeps the lower endpoint of a two-sided
  interval and forgets the deadline. `Traces/Timed/*` and
  `Traces/Subsets/RightSided.agda` measure a set of traces by a duration; the
  sets are read disjunctively, so a cap measures its slowest listed run and a
  floor its fastest.

- `Syntax/Grades/Example/System/Counts/` relates the trace grades to the
  counts. `Subsets/AtMost.agda` and `Subsets/AtLeast.agda` project the subset
  cap onto, respectively, the greatest and the least count among the listed
  traces at each counter. `Lifted/LeftSided.agda` is the generic construction,
  from antichains of guarantees to at-least counts, at any trace order in which
  covering a demand never takes fewer operations; `Timed/LeftSided.agda`
  instantiates it at the coverage floor. `Timed/RightSided.agda` is a negative
  result: going up the allowance order an operation becomes a delay that
  covers it, so every morphism into at-most counts sends every bound to the
  unit. `Time.agda` shows that no count grade projects onto time (every `n`
  steps is the unit), and that pairing counts with time by `_×ᵍ_` and a
  weighted sum preserves all of the structure except the join.

- `Syntax/Grades/Example/Worked/` instantiates the above at one alphabet, a
  sensor node with the operations `read` (1 tick), `write` (2–3) and `send`
  (4–6), and exhibits as checked terms the orderings between concrete grades
  and the action of each morphism on them. `Operations.agda` fixes the
  alphabet and its runs; `Operations/Footprint.agda` the security level each
  operation touches (`send` touches the network, `High`) and the energy it
  draws (`read` 1, `write` 2, `send` 5); `Time/*`, `SecurityLevel.agda`,
  `Product/*`, `Traces/*` and `Counts/*` give the orderings grade by grade;
  `Spec.agda` gives a language specification over the alphabet; and `System/*`
  computes the projections, including the morphisms of the counts under
  `System/Counts/*`. Positive and negative claims are both discharged by
  running the relevant decision procedure.

- `Syntax/Grades/Example/Worked/Typing/` fixes a language over that alphabet
  and types example computations at these grades, using operations,
  sequencing, `delay`, `if`, pattern matching, functions, `box`/`unbox` and
  effect handlers. Each of the twelve instances (the three discrete time
  grades and dense right-sided time; the four trace grades; left-sided time
  with a security level; right-sided time with an energy budget; and at-most
  and at-least counts; each over its identity grade system) writes its
  programs out at its own grades and discharges every side condition (`var`'s
  bound, `unbox`'s premise, `coerce`'s ordering) where the rule imposes it, by
  the grade's decision procedure; where a grade refuses a program, a
  refutation of the required bound stands in its place. The index
  `Typing.agda` states, for each instance, the meaning of a box and whether an
  ordinary variable goes stale. `Typing/Core.agda` contains the language, the
  three ways of meeting `var`'s bound, and the operation clauses passed to
  `handle`. It also records the interaction of sub-effecting with the
  modality: sequencing locks its continuation by the grade at which its first
  part is *typed*, so coercing that part can only restrict what the
  continuation may unbox (`coercion-only-closes`).

### Core language, type system

- `Syntax/BaseTypes.agda` defines the signature of base types (with decidable
  equality, eternal base types, and constants).
- `Syntax/GroundTypes.agda` defines ground types (the parameter and arity types
  of operations), including the temporal modality `[ ρ ]ᵍ A` on ground types.
- `Syntax/Operations.agda` defines operation signatures: the parameter and
  arity ground types of each operation and its (maximal) execution grade.
- `Syntax/Types.agda` defines value and computation types.
- `Syntax/Contexts.agda` defines variables and structured contexts, including
  the context former `Γ ⟨ ρ ⟩` for the passage of a grade.
- `Syntax/Subtyping.agda` defines shape-preserving subtyping of value and
  computation types, `_<:ᵛ_` and `_<:ᶜ_`, contravariant in a function's domain
  and a box's grade and covariant in a computation's effect. It is a preorder
  on types, and a partial order where the grade orders are antisymmetric
  (`<:ᵛ-antisym`). The module also defines least upper bounds of types, `_⊔ᵛ_≡_` and
  `_⊔ᶜ_≡_`, as inductive relations. They are partial: in the contravariant
  positions (a function's domain and a box's grade) the two types coincide,
  a join there being a meet of value types or of resource grades, which the
  grades do not have. The only component that is joined is a computation's
  effect, where `_⊔ₑ_` is total.
- `Syntax/Language.agda` defines well-typed values and computations.
- `Syntax/Renamings/` defines context renamings: `Base.agda` the generating
  calculus (eternal contexts and the `Ren` datatype, indexed by an *ambient*
  context that it fixes), `Equivalence.agda` the equivalence of renamings
  (`_≐ʳ_`), `Coherence.agda` the laws of the action with respect to it, and
  `Category.agda` the resulting categorical structure.
- `Syntax/RenActions.agda` defines the action of renamings on well-typed terms.
- `Syntax/Terms/Equivalence.agda` states that equality of terms is
  propositional equality: the data of a term that no rule inspects (the grade
  bounds of `var` and `unbox`, and the ordering of `coerce`) is
  proof-irrelevant. The congruences are `cong`/`cong₂`, and only the three
  irrelevance laws and `handle-≡` are named. `Syntax/Terms/Transport.agda`
  transports a term along an equality of contexts.
- `Syntax/Substitutions/` defines parallel substitutions and their
  metatheory: `Base.agda` the substitutions, `Lookup.agda` their action on a
  variable, `Action.agda` their action on terms, `Equivalence.agda` their
  equivalence, `Chain.agda` and `ChainEquivalence.agda` their composition,
  `Interchange.agda` the commutation of renaming and substitution, `Laws.agda`
  the resulting laws, and `Subsumption.agda` subsumption for contexts (a
  computation over a binder of `A` is one over any subtype of `A`).
  `Variables.agda`, `At.agda` and `Clauses.agda` specialise these to
  substitution at a context's prefix boundary; `Syntax/Substitutions.agda`
  re-exports them, with the replacement of a single variable as notation.
- `Syntax/CompContext.agda` defines computation term contexts and evaluation
  contexts.

### Operational semantics, progress and preservation theorems

- `OperationalSemantics/State.agda` defines the states of the stateful,
  temporally aware operational semantics, with auxiliary results.
- `OperationalSemantics/PreservationTheorem.agda` defines the small-step
  reduction relation on well-typed computations; being defined on well-typed
  computations, it is itself the preservation theorem.
- `OperationalSemantics/ProgressTheorem.agda` proves the progress theorem.
- `OperationalSemantics/TopLevelOpSemantics.agda`,
  `TopLevelPreservationTheorem.agda` and `TopLevelProgressTheorem.agda` give a
  top-level operational semantics, which interprets unhandled algebraic
  operations, with the corresponding preservation and progress theorems.

### Equational theory

- `EquationalTheory/EquationalTheory.agda` defines an equational theory for the
  language, following the standard equational presentations of local state.
- `EquationalTheory/Alignment.agda` shows that the syntactic equivalence of
  terms is contained in the equational theory.

### Denotational semantics

- `DenotationalSemantics/Model/` gives the abstract model interface over which
  the interpretation is parameterised: `Category.agda` the ambient category,
  `World.agda` the Kripke frame of worlds (a single family of preorders
  `_⊑[ ρ ]_` graded by the resource grades; the frame carries no monoid
  structure), `Modality/{Future,Past,Adjunction,Eternal}.agda` the box and
  context modalities and the adjunction between them, `GroundTypes.agda` and
  `GroundEternal.agda` the interpretation of ground types, `Monad.agda` a
  graded monad with algebraic operations and handling, which folds a handler
  into an algebra (with `Monad/Enrichment.agda` relating its strength to an
  enrichment), `TickMonad.agda` the monad of the top-level machine, and
  `Implementation.agda` the combined interface.
- `DenotationalSemantics/Model/Example/PSh/` is a concrete model on
  setoid-valued presheaves over the worlds: `Base.agda` the category,
  `Modality/*` the modalities, `Monad/*` the effect-tree monad with its
  handling and laws, and `TickMonad.agda`, `Implementation.agda` and
  `TopLevelInstance.agda` the instances.
- `DenotationalSemantics/Model/World/` gives constructions on frames:
  `Product.agda` the product of two frames, `Reindex.agda` reindexing along a
  lax monoid map of grades or a map of worlds, and `Action.agda` the action of
  a grade on itself by right multiplication, `w ⊑[ ρ ] w'` iff `w' ≾ w · ρ`,
  with `forward` restricting a frame to the moves along a preorder on its
  worlds.
- `DenotationalSemantics/Model/Example/World/` gives concrete Kripke frames for
  the example grades, in four families: `Ticks/*`, whose worlds are elapsed
  time (discrete or dense); `Tallies/*`, per-counter counts; `Labels/*`, the
  security level reached; and `TraceHistory/*`, the run so far. `Product/*`
  pairs them for the product grades.
- `DenotationalSemantics/Interpretation/` interprets the language in any such
  model (`Types.agda`, `Contexts.agda`, `Variables.agda`, `Terms.agda`) and
  proves the interpretation coherent with the syntactic structural operations:
  `Renaming/` and `RenamingCoherence.agda` for renamings, and
  `SubstitutionCoherence/` for substitutions. `State.agda` interprets the
  states of the operational semantics.

### Soundness and adequacy

- `EquationalTheory/Soundness.agda` (with `Soundness/`) proves the equational
  theory sound for the denotational semantics: every derivable equation
  `M == N` denotes an equality of morphisms `⟦M⟧ ≈ᵐ ⟦N⟧`.
- `OperationalSemantics/Soundness/Preservation.agda` (with `Preservation/`)
  proves the small-step semantics sound: a step relates denotationally equal
  configurations, a configuration `⟨ S , M ⟩` denoting `M` with its context
  filled by the state. `Soundness/TopLevelPure.agda` proves the same for the
  pure top-level machine.
- `OperationalSemantics/Adequacy/` proves the converse: two programs with
  equal denotations halt with the same shape, at the same operation, and with
  the same answer. The proof combines `Normalization.agda` (existence of a weak
  head normal form), the soundness above, and head faithfulness
  (`HeadFaithful.agda` abstractly, `PSh/*` for the presheaf model), over the
  logical relation of `Reducibility.agda` and `Environment/`.
  `Adequacy/Equational.agda` derives from it that the equational theory is
  observationally sound.

### Type inference

Type inference for the open calculus, by constraint generation and constraint
solving, in the style of HM(X) and of Pottier and Rémy's presentation of ML
type inference.

- `TypeInference/Scopes.agda` defines scopes of variables: one counter each for
  type, resource-grade and effect-grade variables; every scope extension
  reduces definitionally.

- `TypeInference/OpenSyntax/` is the open calculus. `Grades.agda` defines open
  grade expressions: variables, embedded closed grades, products, binary
  joins, and (for resource grades) the image of an effect expression under
  `mapᵉ`. `Types.agda` and `Contexts.agda` define open types and contexts, with
  `ContextsLemmas.agda` for lookup under weakening and substitution, and
  `Subst.agda` substitutions between scopes. `Hyps.agda` defines hypothesis
  sets and entailment: convertibility `_≡̂_` (constants up to `_≃_`), entailed ordering
  `_⊩_≾̂ᵣ_`/`_⊩_≾̂ₑ_` (including the zero-product laws of the grades),
  eternality, the var-rule disjunction `VarOK`, and shape-preserving subtyping
  of open types. `Language.agda` defines the qualified judgement
  `Q ∣ Γ ⊢C⦂ C`: the rules of `Syntax/Language.agda` over open types, with
  side conditions entailed from `Q`, `handle` typing its operation clauses at a
  rigid effect variable, and two rules, `annᵛ` and `annᶜ`, recording a type
  annotation.

- `TypeInference/Raw/Syntax.agda` defines raw terms, untyped and scoped by the
  grade and type variables of the context; `box` carries its grade, an
  expression over that scope. The optional type annotations, of a value
  (`V ⦂ᵛ A`) and of a computation (`M ⦂ᶜ C`), are the only annotation forms;
  they are open types over that scope, each fixing a shape against which
  generation checks the term. `Raw/Subst.agda` defines substitution into
  the annotations. `TypeInference/Erase.agda` erases a derivation to a raw
  term.

- `TypeInference/Constraints/` defines the constraint language (value-type
  subtyping, grade orderings, eternality, the var-rule disjunction, `∃` over
  the three sorts, a rigid `∀ᵉ`, and a conjunction over operations) and
  satisfaction `σ ⊨[ Q ∣ R ] C` relative to hypotheses `Q` and obligations `R`.
  A type equation `A ≐ᵥ B` is subtyping in both directions.

- `TypeInference/Generate.agda` generates a constraint from a raw term and an
  expected type, which is an upper bound. Generation is sound
  (`Soundness.agda`: a solution elaborates to a derivation erasing to the
  term) and complete (`Completeness.agda`: a derivation satisfies the
  constraint generated from its erasure); `charV`/`charC` state both.

- `TypeInference/Solver.agda` axiomatises a constraint solver. Its outcome
  (`Outcome.agda`) is a solution, a refutation, or `stuck`. A solution
  `(σ , Q , R)` solves the constraint (`solve-sound`) and is principal at each
  closed instance (`solve-principal`); a refutation leaves no solution under
  satisfiable conditions (`solve-refutes`). Nothing is claimed of `stuck`.

- `TypeInference/Principality.agda` defines `PrincipalScheme Γ M`, a principal
  type scheme `∀ Θ̃. Q̃ ∧ R̃ ⇒ X̃` whose every instance types `M`
  (`instantiate`) and through which every typing of `M` factors at each closed
  instance (`factor`). `Typable Γ M` is a typing under satisfiable hypotheses,
  and `typable-⇔` states `Typable Γ M ⇔ Satisfiable Q̃ R̃`. `Inference Γ M` is
  `typed`, `untypable` or `stuck`.

- `TypeInference/OpenSyntax/Instances.agda` gives the semantics of the open
  calculus by closed instances `δ : Subst Θ ∅ˢ`. Satisfaction `δ ⊨ Q ∣ R` is
  derivability from no hypotheses at `δ`, each clause's rigid remaining a
  parameter; an obligation `∀ᵉ j₁ … jₖ. Q` holds when `Q` is derivable at fresh
  rigids. `Satisfiable` and semantic entailment `_⊨ᴴ_` are defined through it.
  The central lemma (`val-≾ᵣ`, `val-≾ᵣ⁻` and their companions) states that, at
  closed expressions, entailed ordering is the carrier's ordering of values and
  convertibility is equivalence of values. Closed subtyping, eternality and
  `VarOK` are decidable.

- `TypeInference/SolverImpl.agda` is the concrete solver (`solver : Solver`),
  over an enumeration of the operations (`SolverImpl/Enum.agda`), with its
  report and inference. Its banner lists the stages and the lemmas stating the
  contract of each. `SolverImpl/`:
  - `Solve.agda`: the driver. Subtyping demands, type equations included, are
    expanded and decomposed; eternality demands and the type side of var-rule
    disjunctions are decided when pushed; other atoms are residualised. At the
    close of a rigid scope, each atom is kept, discharged or deferred. A
    solution carries its witness; `Principal.agda` proves it principal
    (`solve-principal`) and a refutation sound (`solve-fail`), stage by stage.
  - `Localise.agda`: values for the unknowns local to a rigid scope, keeping
    every instance entering it (`Localised`); principal for lowering and for
    the unit (`lowerᵉ-least`), instance-preserving only for raising and for
    the top. Each strongly connected component of the orderings between whole
    unknowns is collapsed to one unknown in a single step (`collapse`,
    `equal-⊩`).
  - `Reach.agda`: the reflexive–transitive closure of a finite graph by
    Warshall's algorithm, each entry a chain of edges (`reach`, `rep`), and
    cycle elimination over a policy of preferred and movable vertices
    (`Collapse`, `equal`); sound by construction, completeness not proved.
  - `Deferred.agda`: deferred rigid conditions `∀ᵉ j₁ … jₖ. O`, retried after
    each close (`retry-princ`, `retry-fail`) and read back as obligations.
  - `Entail.agda`: entailment of grade orderings from a hypothesis set, at
    explicit strengths (`Strength`: `closed`, `derive`, `atomic`;
    `decideᵣ`/`decideₑ`), along the hypothesis graph whose edges hold where
    the hypotheses do (`edgeᵣ-sound`, `edgeₑ-sound`); every decision is sound
    by construction, completeness not claimed. Also the closed check, which
    decides the atoms without unknowns and the closed orderings joined by
    chains by the grade's `_≾?_` (`checkClosed-⊩`, `checkClosed-fail`), and
    refutation of an ordering against the unit by the zero-product law
    (`refute≾u`, `refute-⊩`).
  - `Product.agda`, `Normal.agda`, `Canon.agda`: the sum-of-products normal
    form, with products sorted at commutative grades (`nrmᵣ-≡`); the
    reachability table and the embedding of products that `Entail`
    instantiates; and the canonical form of reported grades
    (`canonᵣ-≡`), in which a product with the top is the top where the unit is
    least, and of hypothesis sets, in which each join on a left side is split
    (`canonᴴ-⊩`, `canonᴴ-⊩⁻`). Two products are compared by an ordered
    embedding `_⊑ᵖ_` (match, skip an atom above or below the unit, absorb into
    an atom above the top, merge constants across a skipped atom), and at
    commutative grades as multisets (some permutation of the left side embeds
    in order into the right; `pick`, `absorbAt`). `prodˢ≾` decides the
    embedding (`prodˢ≾-complete`, `prodˢ≾-exact`), which is sound for
    entailment (`⊑ᵖ-sound`).
  - `Simplify.agda`: settles var-rule disjunctions, drops a disjunction
    entailed by another, and prunes entailed atoms of a report (`simplify-⊩`,
    `simplify-⊨`).
  - `Values.agda`: the value rules shared by `Localise` and `Eliminate`, over
    a sort (the expressions of one grade sort read for an unknown) and an
    oracle (whether the unknown may decrease or increase): lowering to the
    join of the lower bounds, raising to the first upper bound that caps the
    others, the least element, the top, the forced unit and equating, each a
    proposition with its decider. Lowering, the least element, the forced
    unit and equating are principal; raising and the top keep every
    instance. Each value keeps every ordering, read at an instance or by
    entailment (`lower-keeps`, `raise-keeps`, `raise-free`, `equal-keeps`);
    an ordering valid at every instance bounds nothing.
  - `Eliminate.agda`: elimination of unknowns from a report in the
    prototype's order (Pottier, ICFP 1996): equating, lowering and raising by
    the rules of `Values` under a polarity oracle, the forced unit (where the
    unit is least; through the image `∣ε∣` where the grade system reflects the
    order at the unit, `reflects-u?`), cycle elimination sending the type
    variables of each strongly connected component of the subtyping atoms to
    its representative (`collapseᵗ`, by `Reach`'s `Collapse`), and lowering a
    type variable. Each step is an `Elim`.
  - `Strengthen.agda`: a report over the variables occurring in it
    (`Strengthened`); `Vars.agda`: sets of variables.
  - `Resid.agda`, `State.agda`, `Polarity.agda`: residual constraints and
    their exact decomposition (`SubDec`, `EtsDec`, `toHyps-compl`), the solver
    state, and the polarity of an unknown.
  - `Expand.agda`: expansion of type unknowns to the shape of their skeletons
    (`expandSub-dec`, `expandSub-max`).
  - `Core/`: first-order unification of skeletons after McBride, sound and
    most general (`unifyᵏ-sound`, `unifyᵏ-max`); decoration of a skeleton with
    fresh grade variables (`Decorate.agda`); occurrence checks and
    strengthening away from a rigid variable (`Occurs.agda`, `Rigid.agda`).

- The end-to-end theorem (`SolverImpl.agda`): `infer Γ M : Inference Γ M`;
  `infer-typed`: a `typed p` verdict satisfies
  `Typable Γ M ⇔ Satisfiable Q̃ R̃`; `infer-untypable`: an `untypable` verdict
  implies `¬ Typable Γ M`; `infer-complete`: a typable term is never
  `untypable`.

- The solver reads `u-least?` and `·-comm?` from the grade system.

- `stuck` arises only where a clause's scope closes with a local unknown to
  which `Localise` assigns no value. Before assigning values, `Localise` puts
  every grade expression of the constraints in normal form, splits each
  ordering whose left side is a join into one ordering per alternative, and
  collapses the cycles of orderings between whole local unknowns. An unknown
  with several upper bounds is sent to one decided below the others. The known
  cases of `stuck` are: a local cycle through a compound side, such as a
  product with the clause's rigid; a local unknown of an outer clause on both
  sides of a deferred condition of an inner clause; and a clause-local unknown
  with no lower bound and several upper bounds, none decided below the others,
  which in a program arises only from `absurd`.

- `TypeInference/Examples/` runs inference on nine functions of the
  prototype's standard library. `Stdlib.agda` proves, over an arbitrary
  language, that inference answers `typed` for each; `Stdlib/` checks the
  schemes by `refl` at four grades, which cover the combinations of `u-least?`
  and `·-comm?`. `Scheme.agda` writes schemes as `∀[ a , b , c ] C ⟹ X`.
  `Annotations.agda` gives programs annotated by `⦂ᵛ` and `⦂ᶜ`, a parameter
  annotation among them, each with the type the annotation forces;
  `Annotations/` checks the schemes at the four grades.
  `Handlers.agda` gives handlers without annotations. `relay`, whose clause
  resumes through the identity applied to its own result, and `relay-boxed`,
  whose clause passes the boxed continuation through the identity twice,
  leave cycles of clause-local unknowns, of latent effects and of box grades,
  which `Localise` collapses; both are typable at every grade. `discard`, whose
  clause discards its continuation, is typable where the unit is least;
  `resume-twice`, whose clause calls it twice, where the unit is the top.
  `Handlers/` checks by `refl`, at the four grades, that inference types each
  program where it is typable (with a derivation at that grade) and refutes it
  elsewhere. `Boxes.agda` gives boxes and delays: claims made early, on time
  and late, after operations, in both branches of an `if`, through nested
  boxes and inside a handler clause, with the box's grade given or inferred;
  and a box that escapes through `return` and is claimed out of time, refuted
  through the transitive closure of the closed orderings. `Boxes/` checks the
  verdicts and schemes at the four grades. `Durations.agda` gives boxes
  claimed after two delays of rational durations, and a box grade inferred
  over them; `Durations/` checks them at dense left- and right-sided time.
  `Reports.agda` gives two schemes that the report simplifies: a var-rule
  disjunction entailed by another, and a product with the top absorbed. `Reports/` checks them at the right-sided
  grades, where the unit is least and the simplifications apply.
  `Stages.agda` tests single solver stages on hand-written constraints, for
  steps that the example programs exercise only in part or not at all:
  splitting joins on the left of
  hypotheses (`canonᴴ`), pruning disjunctions (`walkᵈ`), absorption by the top
  (`canonᵣ`/`canonₑ`), multiset comparison of products (`decideₑ`), the closed
  check through chains (`checkClosed`), the collapse of a clause-local cycle
  on which lowering alone is stuck, and the value of lowering at each shape of
  cycle. `Product.agda` gives programs at time
  paired with a security level (`Product/LeftSidedTimeLevel`,
  `Product/RightSidedTimeLevel`): an embargoed report claimed in time and
  untainted, out of time, and after a `High` operation; a branch whose box
  grade is the join of two levels; a higher-order function whose scheme
  carries both components; and a reading reused after an operation.
