------------------------------------------------------------------------
-- The timed-trace toolkit that the trace-based grades are built      --
-- from.                                                              --
--                                                                    --
-- A timed trace records one run of a computation as it is observed   --
-- from outside: an alternation of delays and operations. The toolkit --
-- supplies non-empty finite sets of such traces, the runs a          --
-- computation may have, with the language product, the orders on     --
-- traces, and the antichain normal forms a set is cut down to under  --
-- an order. The `Banked.*` and `FiniteRunSets.*` grades of           --
-- `Grades.Examples.Traces` are built on these sets, each with its    --
-- own carrier: antichains for a floor, antichains with an added      --
-- greatest point for a cap, and their consistent pairs; the finite   --
-- run set cap is sets with an added greatest point. The regular      --
-- trace languages and the timed regex grades are represented by      --
-- automata and expressions.                                          --
--                                                                    --
-- Nothing here is itself a grade. The module is only an index:       --
-- everything is parameterised by the alphabet `Op`, and the trace    --
-- layer also by the time domain of its delays, so it lists the       --
-- pieces rather than re-exporting them.                              --
------------------------------------------------------------------------

module Grades.Traces where

------------------------------------------------------------------------
-- Traces and sets of traces

-- Strictly positive durations of a time domain, which a delay carries;
-- independent of the alphabet.

import Grades.Traces.Positive

-- Timed traces, their sequencing monoid, its conicality and left
-- cancellation, and decidable equality of traces.

import Grades.Traces.Base

-- Non-empty finite sets of timed traces, which the banked and finite
-- run set grades are built on, with the language product as their
-- monoid and the subset preorder on the underlying lists. A set is held
-- canonically, as the list of its members in increasing lexicographic
-- order, so it is determined by which traces it names.

import Grades.Traces.Sets

-- Restriction along a predicate on operation names, which turns a set
-- of traces over one alphabet into one over a sub-alphabet.

import Grades.Traces.Restriction

-- A strict total order on traces, lexicographic over a strict total
-- order on the alphabet. It enumerates the runs; it does not compare
-- them, so it is unrelated to the orders collected below.

import Grades.Traces.Lexicographic

------------------------------------------------------------------------
-- Measuring time
--
-- How long a trace takes, relative to an assignment of an running time
-- to each operation symbol.

-- The per-trace duration, shared by both set-level aggregations below.

import Grades.Traces.Durations

-- Worst-case (`⊔`) and best-case (`⊓`) aggregation over a set of
-- traces, which together bound a set by a time interval.

import Grades.Traces.MaxDuration
import Grades.Traces.MinDuration

------------------------------------------------------------------------
-- What an order on traces has to supply
--
-- The interface the grades take their order from, in two layers: the
-- order-theoretic half, which the converse also meets, and the facts
-- about the unit. Each order below meets it once and inherits the
-- set-level construction with all its laws.

import Grades.Traces.Order

-- Antichain normal forms: a set of traces cut down to the members that
-- are minimal for the order, so that two sets with the same closure
-- become the same list. It asks only for the order-theoretic half of
-- the interface, so it is taken at either handedness.

import Grades.Traces.Reduced

-- Antichains carried along a map of traces that is a monoid morphism
-- and monotone, normalising before or after mapping being the same.

import Grades.Traces.Embedding

------------------------------------------------------------------------
-- The two orders on traces
--
-- Both are indexed by a running duration and share the arithmetic that
-- manipulates it.

-- The slack arithmetic and the size measure the two relations induct
-- on, stated once.

import Grades.Traces.Slack

------------------------------------------------------------------------
-- Staying inside an allowance
--
-- The allowance order: when a bound permits a run. The bound's
-- operations are permissions and its delays are a budget, which the run
-- spends on its own idling and on operations the bound does not name,
-- at their running time. Budget does not cross an operation the bound
-- names, so a bound says when its slack is available and not merely how
-- much of it there is.

import Grades.Traces.Allowance

-- Its antisymmetry, which also asks every operation to cost something:
-- a free operation would be performed out of an empty budget, and the
-- empty bound would then permit a run different from itself.

import Grades.Traces.Allowance.Antisym

-- That this is needed, checked: at a cost model with a free operation,
-- the empty bound permits a run different from itself, so `≼-ε-inv`
-- and `≼-antisym` both fail.

import Grades.Traces.Allowance.ZeroCost

-- Its interface instance, which asks every operation to cost
-- something: that is what makes the empty bound permit nothing but the
-- empty run, and what the grades' unit-product law rests on.

import Grades.Traces.Allowance.AsOrder

------------------------------------------------------------------------
-- Covering a guarantee
--
-- The coverage order: when a run covers a trace. Every operation the
-- trace names must occur in the run, in order, never bought with time,
-- and every delay it names is met by what the run does
-- between the same two operations it names. Slack does not cross a
-- named operation, so a demand for time is met only where it is placed.
--
-- This is the order a guarantee wants. It is not the converse of the
-- allowance order.

import Grades.Traces.Coverage

-- Its antisymmetry, counting the operation nodes a run performs.

import Grades.Traces.Coverage.Antisym

-- Its interface instance, which needs no assumption about `costˡᵒ`: an
-- operation is never bought, so at any cost model the order is
-- antisymmetric and a spent run covers only the empty guarantee.

import Grades.Traces.Coverage.AsOrder

------------------------------------------------------------------------
-- A guarantee and an allowance together
--
-- Run consistency: some run covers the guarantee and stays within the
-- allowance. The run is eliminated by walking the two together, slack
-- and budget in hand, which decides it.

import Grades.Traces.RunConsistency

------------------------------------------------------------------------
-- An order that carries no grade
--
-- The prefix order, and a checked proof that the language product is
-- not monotone for it, so `·-monoˡ-≾` fails. Any order demanding
-- contiguity fails the same way.

import Grades.Traces.Prefix

------------------------------------------------------------------------
-- Across time domains

-- Traces along a morphism of durations that keeps positive durations
-- positive: a monoid morphism, scaling durations, monotone for both
-- orders at the mapped costs.

import Grades.Traces.Along

-- Running times of operations as intervals, each end open or closed,
-- and the costs read off their closed hull.

import Grades.Traces.RunningTimes

-- Run consistency over graphs of guarantees and allowances: a walk
-- through a cycle of the guarantee is dominated by one without it.

import Grades.Traces.RunConsistency.Cycles
