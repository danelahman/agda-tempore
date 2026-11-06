------------------------------------------------------------------------
-- A trace-history Kripke frame for the timed regex grades in whole   --
-- steps, as upper bounds.                                            --
--                                                                    --
-- Worlds are timed traces. A grade `U` reaches the histories         --
-- extending the current one by a continuation whose reading is below --
-- `U` (`World.History`):                                             --
--                                                                    --
--   w ⊑ʰ[ U ] w'   iff   Σ[ s ] w ∙ s ≡ w'  and  ⟦ s ⟧ ≾ U           --
--                                                                    --
-- An operation is read as its literal, a delay of `d` steps as `d`   --
-- idle waits of at most a step.                                      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)
import Grades.Traces.RunningTimes as RunningTimes

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Nat.UpperBound
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Grades.Examples.Traces.TimedRegex.Nat.UpperBound Op n code name name-code code-name running
  using (upper-bound)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Nat.Base
  Op n code name name-code code-name running
  using (‵ᵍ)

open import MonomorphicCalculus.DenotationalSemantics.Model.World.History ℕᵀ Op upper-bound ‵ᵍ public
