------------------------------------------------------------------------
-- Matrices over modes with entries in an equivariant dioid, and the  --
-- grade of the mode matrices. This module is only an index.          --
------------------------------------------------------------------------

module Grades.Matrix where

import Grades.Matrix.Dioid       -- idempotent semirings
import Grades.Matrix.Modes       -- modes, swaps, representatives
import Grades.Matrix.Nominal     -- equivariant dioids, orbit joins
import Grades.Matrix.Matrices    -- matrices, product, join, order
import Grades.Matrix.Fields      -- matrices of entries naming no modes
import Grades.Matrix.Restrict    -- sub-dioids of the elements with a property
import Grades.Matrix.Boxes       -- boxes over a grade, by name and as a whole
import Grades.Matrix.ModeGrade   -- total matrices of changes as a grade
import Grades.Matrix.ModeClosure -- their closures over the trivial action
