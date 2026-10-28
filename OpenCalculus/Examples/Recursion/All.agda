------------------------------------------------------------------------
-- Primitive recursion on natural numbers and lists: pure recursions; a
-- countdown and a tick per element, whose effects absorb themselves (`ε
-- · ε ≾ ε`); a function refused in the step; a head usable after a pure
-- step and refused, as a box, after a tick; recursion inside an
-- operation clause (`Generate`, `Localise`, `Search`).
------------------------------------------------------------------------

module OpenCalculus.Examples.Recursion.All where

import OpenCalculus.Examples.Recursion

import OpenCalculus.Examples.Recursion.Time.RightSided
import OpenCalculus.Examples.Recursion.Time.LeftSided
