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
-- Fitting inside a schedule
--
-- The sub-trace preorder: when one trace fits inside the schedule
-- another describes, with operations charged the time they take.

import Syntax.Grades.Traces.Subtrace

-- Its two lifts to sets of traces -- Hoare and Smyth -- which the
-- trace-based grades pick their orders from.

import Syntax.Grades.Traces.SubtraceLift

-- A sub-trace is no longer than its host, up to the slack it was
-- granted -- what connects the preorder to the durations above.

import Syntax.Grades.Traces.SubtraceDuration

-- Comparing the preorder across two cost models: raising the cost of
-- an operation narrows the order.

import Syntax.Grades.Traces.SubtraceCost
