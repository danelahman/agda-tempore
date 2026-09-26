------------------------------------------------------------------------
-- Worked instances of the interval grades.                           --
--                                                                    --
-- The running example is the `uplink` run of the sensor node: read,  --
-- idle two ticks, send. Under `opTime` it takes between 7 and 9      --
-- ticks: read 1, the idle 2, and send between 4 and 6. Each interval --
-- grade records part of this:                                        --
--                                                                    --
--   left-sided   [ 7 ,+∞⟩       "at least 7 ticks have passed"       --
--   right-sided  [0, ↑ 9 ]      "at most 9 ticks have passed"        --
--   two-sided    [ 7 , ↑ 9 ]    both bounds at once                  --
--                                                                    --
-- Both upper endpoints range over the extended naturals, so          --
-- `[0, ∞ ]` and `[ 7 , ∞ ]` impose no upper bound.                   --
--                                                                    --
-- In each grade `_·_` adds the endpoints, so sequencing two runs     --
-- adds their windows, and the order is *weakening*: a grade lies     --
-- below the grades that claim less. The modules below give the       --
-- direction of weakening and the greatest element `⊤` of each grade. --
--                                                                    --
-- An index: one module per grade.                                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Time where

-- discharging the numeric side conditions the sections below reduce to

import Syntax.Grades.Example.Worked.Time.Decide

-- "at least `n` ticks have passed"

import Syntax.Grades.Example.Worked.Time.LeftSided

-- "at most `n` ticks have passed"; the mirror image

import Syntax.Grades.Example.Worked.Time.RightSided

-- both bounds at once, including the infinite upper endpoint

import Syntax.Grades.Example.Worked.Time.TwoSided

------------------------------------------------------------------------
-- The dense analogue: units range over an extended rational, not ℕ

-- discharging the numeric side conditions the dense instances reduce to

import Syntax.Grades.Example.Worked.Time.Dense.Decide

-- "at least q units have passed"

import Syntax.Grades.Example.Worked.Time.Dense.LeftSided

-- "at most q units have passed"; the mirror image

import Syntax.Grades.Example.Worked.Time.Dense.RightSided

-- both bounds at once, including the infinite upper endpoint

import Syntax.Grades.Example.Worked.Time.Dense.TwoSided
