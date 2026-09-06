------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                   --
--                                                                     --
-- A grade records *which runs* a computation must or may have. The     --
-- examples form a grid of three axes.                                  --
--                                                                     --
-- First, which order on traces is lifted -- how loosely a listed run   --
-- is matched:                                                          --
--                                                                     --
--   Inclusion       not at all: a run matches by being listed (`_≡_`)  --
--   Subtrace        the lenient sub-trace order, which lets time       --
--                   banked anywhere pay for a delay demanded later     --
--   SubtraceTimed   its time-strict restriction, which pays a delay    --
--                   only out of time spent in the same window          --
--                                                                     --
-- Then, within each of the two sub-trace families, how a listed run is --
-- matched -- the lift:                                                 --
--                                                                     --
--   LowerLift   every trace on the left matched on the right  (Hoare)  --
--   UpperLift   every trace on the right matched on the left  (Smyth)  --
--   Convex      both at once                            (Egli-Milner)  --
--                                                                     --
-- And finally what the set bounds -- the sidedness, mirroring `Time`:  --
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
--                                                                     --
-- Since only the comparison changes along the first axis, the grid is  --
-- built once in `Traces.Lifted`, over an arbitrary trace order, and    --
-- `Traces.Subtrace` and `Traces.SubtraceTimed` instantiate it. That    --
-- `_≡_` is not such an order -- `ε ≡ t` fails -- is exactly why        --
-- `Inclusion` stands outside the axis and is written out separately.   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces where

-- matched exactly

import Syntax.Grades.Example.Traces.Inclusion

-- the grid over an arbitrary trace order

import Syntax.Grades.Example.Traces.Lifted

-- that grid at each of the two sub-trace orders

import Syntax.Grades.Example.Traces.Subtrace
import Syntax.Grades.Example.Traces.SubtraceTimed
