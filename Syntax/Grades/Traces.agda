------------------------------------------------------------------------
-- The timed-trace toolkit that the trace-based grades are built from. --
--                                                                     --
-- A timed trace records one run of a computation as it is observed     --
-- from outside: an alternation of delays and operations. A grade is a  --
-- non-empty finite *set* of such traces -- the runs a computation may  --
-- have -- and every trace-based grade in `Grades.Example.Traces`     --
-- has that same carrier and the same monoid on it. What distinguishes  --
-- them is the order, and the orders are built from the machinery       --
-- collected here.                                                      --
--                                                                     --
-- Nothing in this module is itself a grade; it is the shared layer     --
-- underneath. This module is only an index -- everything is           --
-- parameterised by the alphabet `Op`, and the trace layer also by the  --
-- time domain of its delays, so it lists the pieces rather than        --
-- re-exporting them.                                                   --
------------------------------------------------------------------------

module Syntax.Grades.Traces where

------------------------------------------------------------------------
-- Traces and sets of traces

-- Strictly positive durations of a time domain, which is what a delay
-- carries. Alphabet independent, so it stands alone.

import Syntax.Grades.Traces.Positive

-- Timed traces, their sequencing monoid, its conicality and left
-- cancellation, and decidable equality of traces.

import Syntax.Grades.Traces.Base

-- Non-empty finite sets of timed traces: the carrier every trace-based
-- grade shares, with the language product as its monoid and the subset
-- preorder on the underlying lists. A set is held canonically, as the
-- list of its members in increasing lexicographic order, so it is
-- determined by which traces it names.

import Syntax.Grades.Traces.Sets

-- Restriction along a predicate on operation names, which turns a set
-- of traces over one alphabet into one over a sub-alphabet.

import Syntax.Grades.Traces.Restriction

-- A strict total order on traces, lexicographic over a strict total
-- order on the alphabet. It enumerates the runs; it does not compare
-- them, so it is unrelated to the orders collected below.

import Syntax.Grades.Traces.Lexicographic

------------------------------------------------------------------------
-- Measuring time
--
-- How long a trace takes, relative to an assignment of an execution
-- time to each operation symbol.

-- The per-trace duration, shared by both set-level aggregations below.

import Syntax.Grades.Traces.Durations

-- Worst-case (`⊔`) and best-case (`⊓`) aggregation over a set of
-- traces, which together bound a set by a time interval.

import Syntax.Grades.Traces.MaxDuration
import Syntax.Grades.Traces.MinDuration

------------------------------------------------------------------------
-- What an order on traces has to supply
--
-- The interface the grades take their order from, in two layers: the
-- order-theoretic half, which the converse also meets, and the facts
-- about the unit on top of it. It mentions no particular order, so
-- each order below meets the interface once and inherits the whole
-- set-level construction with all its laws.

import Syntax.Grades.Traces.Order

-- Antichain normal forms: a set of traces cut down to the members that
-- are minimal for the order, so that two sets with the same closure
-- become the same list. It asks only for the order-theoretic half of
-- the interface, so it is taken at either handedness.

import Syntax.Grades.Traces.Reduced

-- Antichains carried along a map of traces that is a monoid morphism
-- and monotone, normalising before or after mapping being the same.

import Syntax.Grades.Traces.Embedding

------------------------------------------------------------------------
-- The two orders on traces
--
-- Both are indexed by a running duration and share the arithmetic that
-- manipulates it.

-- The slack arithmetic and the size measure the two relations induct
-- on, stated once.

import Syntax.Grades.Traces.Slack

------------------------------------------------------------------------
-- Staying inside an allowance
--
-- The allowance order: when a bound permits a run. The bound's
-- operations are permissions and its delays are a budget, which the run
-- spends on its own idling and on operations the bound does not name,
-- at their execution time. Budget does not cross an operation the bound
-- names, so a bound says when its slack is available and not merely how
-- much of it there is.

import Syntax.Grades.Traces.Allowance

-- Its antisymmetry, which also asks every operation to cost something:
-- a free operation would be performed out of an empty budget, and the
-- empty bound would then permit a run different from itself.

import Syntax.Grades.Traces.Allowance.Antisym

-- And the checked negative that makes that hypothesis necessary: at a
-- cost model with a free operation, the empty bound permits a run
-- different from itself, so `≼-ε-inv` and `≼-antisym` both fail.

import Syntax.Grades.Traces.Allowance.ZeroCost

-- Its interface instance, which asks every operation to cost
-- something: that is what makes the empty bound permit nothing but the
-- empty run, and what the grades' zero-product law rests on.

import Syntax.Grades.Traces.Allowance.AsOrder

------------------------------------------------------------------------
-- Covering a guarantee
--
-- The coverage order: when a run covers a trace. Every operation the
-- trace names must genuinely occur in the run, in order -- time never
-- buys one -- and every delay it names is met by what the run does
-- between the same two operations it names. Slack does not cross a
-- named operation, so a demand for time is met only where it is placed.
--
-- This is the order a guarantee wants. It is not the converse of the
-- allowance order; the two are incomparable.

import Syntax.Grades.Traces.Coverage

-- Its antisymmetry, counting the operation nodes a run performs.

import Syntax.Grades.Traces.Coverage.Antisym

-- Its interface instance. Unlike the allowance order this needs no
-- assumption about `costˡᵒ`: an operation is never bought here, at any
-- price, so a spent run covers nothing but the empty guarantee
-- outright, and covers it antisymmetrically at any cost model.

import Syntax.Grades.Traces.Coverage.AsOrder

------------------------------------------------------------------------
-- An order that carries no grade
--
-- The prefix order, and a checked proof that the language product is
-- not monotone for it, so `·-monoˡ-≾` fails. Any order demanding
-- contiguity fails the same way.

import Syntax.Grades.Traces.Prefix

------------------------------------------------------------------------
-- Across time domains

-- Traces along a morphism of durations that keeps positive durations
-- positive: a monoid morphism, scaling durations, monotone for both
-- orders at the mapped costs.

import Syntax.Grades.Traces.Along

-- Running times of operations as intervals, each end open or closed,
-- and the costs read off their closed hull.

import Syntax.Grades.Traces.RunningTimes
