------------------------------------------------------------------------
-- Sets of timed traces compared by inclusion.                         --
--                                                                     --
-- The comparison never consults the sub-trace preorder: a run meets a  --
-- listed one only by being it. This is the one family that needs no    --
-- execution times on the operations.                                  --
--                                                                     --
-- The three grades differ in what the set bounds and, with it, which   --
-- way the inclusion runs:                                             --
--                                                                     --
--   LeftSided    a floor:  Q ⊆ P   -- weakening requires fewer runs   --
--   RightSided   a cap:    P ⊆ Q   -- weakening permits more runs     --
--   TwoSided     a pair of both, compared endpoint by endpoint         --
--                                                                     --
-- The two one-sided grades are the same comparison with the sets       --
-- exchanged. It has to be the *sets* that are exchanged and not the    --
-- relation flipped: `_≡_` is symmetric, so flipping it changes         --
-- nothing, and the two grades would coincide.                         --
--                                                                     --
-- `LowerLift` is this family with the comparison relaxed by `_≼_`, in --
-- the same two argument orders.                                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.Inclusion where

-- a floor: the runs a computation is required to have

import Syntax.Grades.Example.Traces.Inclusion.LeftSided

-- a cap: the runs it is permitted to have

import Syntax.Grades.Example.Traces.Inclusion.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.Inclusion.TwoSided
