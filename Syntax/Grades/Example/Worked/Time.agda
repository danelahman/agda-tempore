------------------------------------------------------------------------
-- Worked instances of the interval grades.                            --
--                                                                     --
-- The sensor node's `uplink` run -- read, idle two ticks, send -- is   --
-- the running example. Under `opTime` it takes between 7 and 9 ticks:  --
-- read 1, the idle 2, and send anywhere from 4 to 6. Each interval     --
-- grade records a different part of that fact:                         --
--                                                                     --
--   left-sided   [ 7 ,+∞⟩       "at least 7 ticks have passed"        --
--   right-sided  [0, ↑ 9 ]      "at most 9 ticks have passed"         --
--   two-sided    [ 7 , ↑ 9 ]    both bounds at once                    --
--                                                                     --
-- Both upper endpoints range over the extended naturals, so `[0, ∞ ]`  --
-- and `[ 7 , ∞ ]` impose no upper bound at all.                        --
--                                                                     --
-- In each case `_·_` adds the endpoints, so sequencing two runs adds   --
-- their windows, and the order is *weakening*: a grade sits below the  --
-- grades that claim less than it does. Which way "less" points differs --
-- per grade, and that is what the sections below pin down. Each grade  --
-- also has a designated greatest element `⊤`, and the sections below   --
-- say which one it is.                                                 --
--                                                                     --
-- An index only: one module per grade.                                 --
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
