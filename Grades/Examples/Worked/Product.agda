------------------------------------------------------------------------
-- Worked instances of the product grades.                            --
--                                                                    --
-- An index only: one module per pairing.                             --
------------------------------------------------------------------------

module Grades.Examples.Worked.Product where

-- left-sided time and a security level: an embargo with a taint check

import Grades.Examples.Worked.Product.LeftSidedTimeLevel

-- right-sided time and a security level: an expiring, untainted
-- capability

import Grades.Examples.Worked.Product.RightSidedTimeLevel

-- right-sided time and an energy budget: a drifting calibration

import Grades.Examples.Worked.Product.RightSidedTimeEnergy
