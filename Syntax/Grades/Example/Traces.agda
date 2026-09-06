------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                   --
--                                                                     --
-- A grade records *which runs* a computation must or may have. The     --
-- examples form a grid of two axes.                                    --
--                                                                     --
-- Across, how a listed run is matched -- the comparison:               --
--                                                                     --
--   Inclusion   by being it                          (`_≡_`)          --
--   LowerLift   by covering it, at the operations'   (Hoare, `_≼_`)   --
--               execution times                                       --
--   UpperLift   the same, quantified over the other  (Smyth, `_≼_`)   --
--               set: each listed bound justified back                 --
--   Convex      both of the two above at once        (Egli-Milner)    --
--                                                                     --
-- Down, what the set bounds -- the sidedness, mirroring `Time`:        --
--                                                                     --
--   LeftSided   a floor, "at least"                                   --
--   RightSided  a cap, "at most"                                      --
--   TwoSided    a pair of endpoints, "between"                        --
--                                                                     --
-- Every cell is built the same way: the cap compares the two sets in   --
-- the order written, the floor compares them exchanged, and the pair   --
-- uses one comparison on each endpoint in those opposite directions.   --
-- That is what makes the columns analogues of one another -- only how  --
-- a run is matched changes -- and it is why `Inclusion` is the whole   --
-- grid at `_≡_`, where `LowerLift` and `UpperLift` coincide.           --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces where

import Syntax.Grades.Example.Traces.Inclusion
import Syntax.Grades.Example.Traces.LowerLift
import Syntax.Grades.Example.Traces.UpperLift
import Syntax.Grades.Example.Traces.Convex
