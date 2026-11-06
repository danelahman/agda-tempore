------------------------------------------------------------------------
-- Worked instances of the product grades.                            --
--                                                                    --
-- An index only: one module per pairing.                             --
------------------------------------------------------------------------

module Grades.Examples.Worked.Product where

-- lower bounds on time and a lattice: an embargo with a taint check

import Grades.Examples.Worked.Product.TimeLowerBoundLattice

-- upper bounds on time and a lattice: an expiring, untainted
-- capability

import Grades.Examples.Worked.Product.TimeUpperBoundLattice

-- upper bounds on time and an energy budget: a drifting calibration

import Grades.Examples.Worked.Product.TimeUpperBoundEnergy
