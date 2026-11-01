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

import PolymorphicCalculus.Examples.Handlers.Time.RightSided
import PolymorphicCalculus.Examples.Handlers.Time.LeftSided
import PolymorphicCalculus.Examples.Handlers.Traces.Timed.RightSided
import PolymorphicCalculus.Examples.Handlers.Traces.Timed.LeftSided
