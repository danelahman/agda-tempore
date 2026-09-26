------------------------------------------------------------------------
-- Worked instances of the product grades.                             --
--                                                                     --
-- An index only: one module per pairing.                               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Product where

-- left-sided time and a security level: an embargo with a taint check

import Syntax.Grades.Example.Worked.Product.LeftSidedTimeLevel

-- right-sided time and a security level: an expiring, untainted
-- capability

import Syntax.Grades.Example.Worked.Product.RightSidedTimeLevel

-- right-sided time and an energy budget: a drifting calibration

import Syntax.Grades.Example.Worked.Product.RightSidedTimeEnergy
