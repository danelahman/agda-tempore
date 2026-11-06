------------------------------------------------------------------------
-- Worked instances of the count grades, at the sensor node.          --
--                                                                    --
-- One counter per operation, in the order `read`, `write`, `send`.   --
-- An at-most count bounds each from above (a rate limit: "at most    --
-- two transmissions"), and an at-least count from below ("three      --
-- readings have been taken", after which a token computed from them  --
-- is available).                                                     --
--                                                                    --
-- An index: `Index` fixes the shared counters, and there is one      --
-- module per family of counts.                                       --
------------------------------------------------------------------------

module Grades.Examples.Worked.Counts where

import Grades.Examples.Worked.Counts.Index

-- "at most k of each operation"

import Grades.Examples.Worked.Counts.AtMost

-- "at least k of each operation"

import Grades.Examples.Worked.Counts.AtLeast

-- "at most k of each operation", by operation name

import Grades.Examples.Worked.Counts.AtMost.ByName
