------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                   --
--                                                                     --
-- A grade records *which runs* a computation must or may have. The    --
-- examples form a grid of two axes.                                   --
--                                                                     --
-- Across, how a listed run is matched -- the comparison:              --
--                                                                     --
--   Inclusion   by being it                    (`_≡_`)                --
--   Subtrace    by covering it, at the         (`_≼_`)                --
--               operations' execution times                            --
--   Convex      as `Subtrace`, and back again  (Egli-Milner)          --
--                                                                     --
-- Down, what the set bounds -- the sidedness, mirroring `Time`:     --
--                                                                     --
--   LeftSided   a floor, "at least"                                   --
--   RightSided  a cap, "at most"                                      --
--   TwoSided    a pair of endpoints, "between"                        --
--                                                                     --
-- Every cell is built the same way: the cap compares the two sets in   --
-- the order written, the floor compares them exchanged, and the pair   --
-- uses one comparison on each endpoint in those opposite directions.   --
-- That is what makes the three columns analogues of one another, the   --
-- relaxation of `_≡_` to `_≼_` being the only thing that changes.     --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces where

import Syntax.Grades.Example.Traces.Inclusion
import Syntax.Grades.Example.Traces.Subtrace
import Syntax.Grades.Example.Traces.Convex
