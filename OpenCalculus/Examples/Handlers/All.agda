------------------------------------------------------------------------
-- Handlers without annotations: two leave cycles of unknowns local to
-- the clause, typed at four grades; one discards its continuation and
-- one resumes it twice, each typed where it is typable and refuted
-- elsewhere. Exercises clause-local unknowns and handlers (`Localise`).
------------------------------------------------------------------------

module OpenCalculus.Examples.Handlers.All where

import OpenCalculus.Examples.Handlers

import OpenCalculus.Examples.Handlers.Time.RightSided
import OpenCalculus.Examples.Handlers.Time.LeftSided
import OpenCalculus.Examples.Handlers.Traces.Timed.RightSided
import OpenCalculus.Examples.Handlers.Traces.Timed.LeftSided
