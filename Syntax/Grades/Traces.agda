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
-- parameterised by the alphabet `Op`, so it lists the pieces rather    --
-- than re-exporting them.                                              --
------------------------------------------------------------------------

module Syntax.Grades.Traces where

------------------------------------------------------------------------
-- Traces and sets of traces

-- Strictly positive durations, which is what a delay carries. Alphabet
-- independent, so it stands alone.

import Syntax.Grades.Traces.Positive

-- Timed traces, their sequencing monoid, its conicality and left
-- cancellation, and decidable equality of traces.

import Syntax.Grades.Traces.Base

-- Non-empty finite sets of timed traces: the carrier every trace-based
-- grade shares, with the language product as its monoid and the subset
-- preorder on the underlying lists.

import Syntax.Grades.Traces.Sets

-- Restriction along a predicate on operation names, which turns a set
-- of traces over one alphabet into one over a sub-alphabet.

import Syntax.Grades.Traces.Restriction

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
-- The interface the grades take their order from, and its two lifts to
-- sets of traces -- Hoare and Smyth. Neither mentions a particular
-- order, so each order below meets the interface once and inherits both
-- lifts with all their laws.

import Syntax.Grades.Traces.Order
import Syntax.Grades.Traces.OrderLift

------------------------------------------------------------------------
-- The two orders on traces
--
-- Both are indexed by a running number of time units and share the
-- arithmetic that manipulates it.

-- The slack arithmetic and the size measure the two relations induct
-- on, stated once.

import Syntax.Grades.Traces.Slack

------------------------------------------------------------------------
-- Staying inside an allowance
--
-- The allowance order: when a bound permits a run. The bound's
-- operations are permissions and its delays are a budget, which the run
-- spends on its own idling and on operations the bound does not name,
-- at their execution time. Going up the order an operation turns into a
-- delay long enough to cover it, and a delay grows. Budget does not
-- cross an operation the bound names, so a bound says when its slack is
-- available and not merely how much of it there is.

import Syntax.Grades.Traces.Allowance

-- Its interface instance and lifts. Both ask every operation to cost
-- something, which is what makes the empty bound permit nothing but the
-- empty run, and what the grades' zero-product law rests on.

import Syntax.Grades.Traces.Allowance.AsOrder
import Syntax.Grades.Traces.AllowanceLift

------------------------------------------------------------------------
-- Covering a guarantee
--
-- The coverage order: when a run covers a trace. Every operation the
-- trace names must genuinely occur in the run, in order -- time never
-- buys one -- and every delay it names is met by what the run does
-- between the same two operations it names. Slack does not cross a
-- named operation, so a demand for time is met only where it is placed.
--
-- This is the order a guarantee wants, and it is deliberately not the
-- converse of the allowance order: there a bound's delays buy the run's
-- operations, which read as a guarantee would let a run that merely
-- idles discharge "a reading was taken". The two are incomparable.

import Syntax.Grades.Traces.Coverage

-- Its interface instance and lifts. Unlike the allowance order these
-- need no assumption about `costˡᵒ`: an operation is never bought here,
-- at any price, so a spent run covers nothing but the empty guarantee
-- outright.

import Syntax.Grades.Traces.Coverage.AsOrder
import Syntax.Grades.Traces.CoverageLift

------------------------------------------------------------------------
-- An order that carries no grade
--
-- The prefix order, and a checked proof that the language product is
-- not monotone for it, so `·-monoˡ-≾` fails. Any order demanding
-- contiguity fails the same way.

import Syntax.Grades.Traces.Prefix

------------------------------------------------------------------------
-- Parked
--
-- The sub-trace orders are under `backup/`, along with their lifts,
-- durations and cost-model comparison, and are imported from nowhere.
