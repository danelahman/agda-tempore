--------------------------------------------------------------------------------
-- Completeness checks at deadlines: a value kept across the resumption, by   --
-- clauses resuming at once and after a tick.                                 --
--------------------------------------------------------------------------------

open import Util.Equality

open import TypeInference.SolverImpl.Demo.TimeIntervals using (uᵈ-min)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Kept where

open M

module Now   = M.Keeping (keepNow uᵈ-min uᵈ-min ans)
module After = M.Keeping (keepAfter τ τₑ τᵣ ans)

ex-h-keep : Verdict Now.h-keep
ex-h-keep = refused refl

ex-h-keep-after : Verdict After.h-keep
ex-h-keep-after = refused refl
