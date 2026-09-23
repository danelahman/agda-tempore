--------------------------------------------------------------------------------
-- Completeness checks at timed traces: a value kept across the resumption.   --
--------------------------------------------------------------------------------

open import Util.Equality

open import TypeInference.SolverImpl.Demo.TimedTraces using (uᵇ-least)

open import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Kept where

open M

open M.Keeping (keepNow uᵇ-least uᵇ-least ans)

ex-h-keep : Verdict h-keep
ex-h-keep = refused refl
