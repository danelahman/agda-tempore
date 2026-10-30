------------------------------------------------------------------------
-- Boxes and delays: claims made early, on time and late, after
-- operations, in branches and in a handler clause, with the box's grade
-- given or inferred; a box that escapes through `return`, claimed out of
-- time and refuted; a box claimed through an annotation. Exercises unbox,
-- on a variable and on an annotated one, the variable rule and closed
-- orderings (`Entail`).
------------------------------------------------------------------------

module PolymorphicCalculus.Examples.Boxes.All where

import PolymorphicCalculus.Examples.Boxes

import PolymorphicCalculus.Examples.Boxes.Time.RightSided
import PolymorphicCalculus.Examples.Boxes.Time.LeftSided
import PolymorphicCalculus.Examples.Boxes.Traces.Timed.RightSided
import PolymorphicCalculus.Examples.Boxes.Traces.Timed.LeftSided
