------------------------------------------------------------------------
-- Worked instances of the count grades, at the sensor node.          --
--                                                                    --
-- One counter per operation, in the order `read`, `write`, `send`.   --
-- An at-most grade is a quota on each (a rate limit: "at most two    --
-- transmissions"), and an at-least grade a count that is certain     --
-- ("three readings have been taken", after which a token computed    --
-- from them is available).                                           --
--                                                                    --
-- An index: `Index` fixes the shared counters, and there is one      --
-- module per family of counts.                                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Counts where

import Syntax.Grades.Example.Worked.Counts.Index

-- "at most k of each operation"

import Syntax.Grades.Example.Worked.Counts.AtMost

-- "at least k of each operation"

import Syntax.Grades.Example.Worked.Counts.AtLeast
