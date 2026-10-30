------------------------------------------------------------------------
-- Handlers without annotations: two leave cycles of unknowns local to
-- the clause, typed at four grades; one discards its continuation and
-- one resumes it twice, each typed where it is typable and refuted
-- elsewhere; three use a handler as a value, bound, taken as an argument
-- and passed. Exercises clause-local unknowns and handlers (`Localise`),
-- and the decomposition of handler types.
------------------------------------------------------------------------

module PolymorphicCalculus.Examples.Handlers.All where

import PolymorphicCalculus.Examples.Handlers

import PolymorphicCalculus.Examples.Handlers.Time.RightSided
import PolymorphicCalculus.Examples.Handlers.Time.LeftSided
import PolymorphicCalculus.Examples.Handlers.Traces.Timed.RightSided
import PolymorphicCalculus.Examples.Handlers.Traces.Timed.LeftSided
