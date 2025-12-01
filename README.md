# Agda formalisation for a generally graded core language for temporal resources

A (work in progress) Agda formalisation of a (Fitch-style) **generally graded, 
modally typed, effectful core language for safe and correct programming with
temporal resources**, i.e., resources that become available only after some 
amount of time, events, etc after being brought into scope, e.g., when an 
assembly operation needs to wait for (car) parts to dry after executing a paint
operation, or for some other actions to happen before executing new operations.

This repository builds on two prior formalisations that only modelled discrete
time passage as the means to specify and verify temporal properties of resources:
[danelahman/temporal-resources](https://github.com/danelahman/temporal-resources) 
and [rzgdmqt/temporal-resources](https://github.com/rzgdmqt/temporal-resources).

In contrast, the core language formalised in this repository can use arbitrary 
(commutative) ordered monoids to verify temporal properties of resources. 
Furthermore, one can use different monoids for grading effects and resources.

The **main features** of this core language are:

- Fitch-style, _temporally-graded modal types_ `[ rho ] X` are used to capture
  temporal resources, expressing that an `X`-typed value will be available in at
  most `rho` time steps, after at most `rho` events, or other similar property.

- A novel notion of _temporally-aware algebraic effects_, where operations'
  specifications include their effect specification, and their continuations 
  know that an operation's worth of additional time, events, etc has happened
  before they start executing, making it possible to safely access further 
  temporal resources in the continuation.

- _Effect handlers_, also temporally-aware, that have to respect the temporal
  discipline of algebraic operations.

- A _graded monads-based modal effect system_ (with some added temporal 
  awareness) that modularly tracks the effects and resource usage.

The formalisation is developed and tested with Agda version 2.8.0 and Agda
Standard Library version 2.3.

The formalisation consists of **three main parts**:

### Core language, type system

The main modules presenting the core language are:

- `Syntax/Grades.agda` defines the notion of grades (for effects and resoruces). 
  (TODO NEW)

- `Syntax/Types.agda` defines types. 
  (TODO ADAPT)

- `Syntax/Contexts.agda` defines contexts and operations on them. 
  (TODO ADAPT)

- `Syntax/Language.agda` defines well-typed values and computations. 
  (TODO ADAPT)

- `Syntax/Renamings.agda` defines renamings and their action on well-typed
  terms. 
  (TODO ADAPT)

- `Syntax/Substitutions.agda` defines the action of substitution on well-typed
  terms. 
  (TODO ADAPT)

- `Syntax/CompContext.agda` defines computation term and evaluation contexts.
  (TODO ADAPT)

### Operational semantics, progress theorem

- `OperationalSemantics/State.agda` defines state for the stateful temporally 
  aware operational semantics, and proves some auxiliary results about states.
  (TODO ADAPT)

- `OperationalSemantics/PreservationTheorem.agda` defines a reduction relation
  for well-typed computations; as the semantics is defined on well-typed
  computations, it simultaneously also proves preservation theorem.
  (TODO ADAPT)

- `OperationalSemantics/TheoremsAboutSteps.agda` proves some basic results
  about the reduction relation.
  (TODO ADAPT)

- `OperationalSemantics/ProgressTheorem.agda` proves progress theorem.
  (TODO ADAPT)

### Equational theory

- `EquationalTheory/EquationalTheory.agda` defines an equational theory for the
  language inspired by the standard equational presentations of local state.
  (TODO ADAPT)

## Work in progress

Agda formalisation of the soundness proof is not yet finished, and remains work
in progress. (TODO ADAPT AND FINISH)
