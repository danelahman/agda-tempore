------------------------------------------------------------------------
-- A trace-history Kripke frame for the rigid timed regular grades in --
-- whole steps, as upper bounds.                                      --
--                                                                    --
-- Worlds are timed traces. A grade `U` reaches the histories         --
-- extending the current one by a continuation whose reading is below --
-- `U` (`World.History`):                                             --
--                                                                    --
--   w ⊑ʰ[ U ] w'   iff   Σ[ s ] w ∙ s ≡ w'  and  ⟦ s ⟧ ≾ U            --
--                                                                    --
-- An operation is read as its literal, a delay of `d` steps as `d`   --
-- strict waits of at most a step.                                    --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Regular.RightSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Syntax.Grades.Example.Traces.Rigid.Regular.RightSided Op n code name name-code code-name running
  using (right-sided)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Regular.Base
  Op n code name name-code code-name running
  using (‵ᵍ)

open import DenotationalSemantics.Model.World.History ℕᵀ Op right-sided ‵ᵍ public
