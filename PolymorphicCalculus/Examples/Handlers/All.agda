------------------------------------------------------------------------
-- Handlers                                                           --
--                                                                    --
-- Handlers written without annotations: a continuation resumed       --
-- through a helper, dropped, or resumed twice, and handlers passed   --
-- around as values.                                                  --
--                                                                    --
-- Exercises: clause-local unknowns (`Localise`) and handler types.   --
------------------------------------------------------------------------

module PolymorphicCalculus.Examples.Handlers.All where

import PolymorphicCalculus.Examples.Handlers

import PolymorphicCalculus.Examples.Handlers.Time.UpperBound
import PolymorphicCalculus.Examples.Handlers.Time.LowerBound
import PolymorphicCalculus.Examples.Handlers.Traces.Banked.UpperBound
import PolymorphicCalculus.Examples.Handlers.Traces.Banked.LowerBound
