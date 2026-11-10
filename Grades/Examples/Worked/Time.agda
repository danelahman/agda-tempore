------------------------------------------------------------------------
-- Worked instances of the time lower bounds, time upper bounds and   --
-- time intervals.                                                    --
--                                                                    --
-- The running example is the `uplink` run of the sensor node: read,  --
-- idle two ticks, send. Under `opTime` it takes between 7 and 9      --
-- ticks: read 1, the idle 2, and send between 4 and 6. Each grade    --
-- records part of this:                                              --
--                                                                    --
--   lower-bound  [ 7 ,+∞⟩     "at least 7 ticks have passed"         --
--   upper-bound  [0, ↑ 9 ]    "at most 9 ticks have passed"          --
--   interval     [ 7 , ↑ 9 ]  both bounds at once                    --
--                                                                    --
-- Both upper endpoints range over the extended naturals, so          --
-- `[0, ∞ ]` and `[ 7 , ∞ ]` impose no upper bound.                   --
--                                                                    --
-- In each grade `_·_` adds the endpoints, so sequencing two runs     --
-- adds their windows, and the order is weakening: a grade lies       --
-- below the grades that claim less. The modules below give the       --
-- direction of weakening and the greatest element `⊤` of each grade. --
--                                                                    --
-- An index: one module per grade.                                    --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time where

-- discharging the numeric side conditions the sections below reduce to

import Grades.Examples.Worked.Time.Decide

-- "at least `n` ticks have passed"

import Grades.Examples.Worked.Time.LowerBound

-- "at most `n` ticks have passed"; the mirror image

import Grades.Examples.Worked.Time.UpperBound

-- both bounds at once, including the infinite upper endpoint

import Grades.Examples.Worked.Time.Interval

------------------------------------------------------------------------
-- The dense analogue: units range over an extended rational, not ℕ

-- discharging the numeric side conditions the dense instances reduce to

import Grades.Examples.Worked.Time.Rational.Decide

-- "at least q units have passed"

import Grades.Examples.Worked.Time.Rational.LowerBound

-- "at most q units have passed"; the mirror image

import Grades.Examples.Worked.Time.Rational.UpperBound

-- both bounds at once, including the infinite upper endpoint

import Grades.Examples.Worked.Time.Rational.Interval

-- one-sided bounds with an open or closed end

import Grades.Examples.Worked.Time.Rational.LowerBoundCut
import Grades.Examples.Worked.Time.Rational.UpperBoundCut
