------------------------------------------------------------------------
-- A trace-history Kripke frame for the rigid timed regular grades in --
-- whole steps, as intervals.                                         --
--                                                                    --
-- Worlds are timed traces, and a grade `[ L , U ]` reaches the       --
-- histories extending the current one by one continuation that both --
-- endpoints admit (`World.History` at the interval grade):           --
--                                                                    --
--   w ⊑ʰ[ [ L , U ] ] w'   iff   Σ[ s ] w ∙ s ≡ w'                    --
--                                  and  ⟦ s ⟧ ≾ L  and  ⟦ s ⟧ ≾ U     --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Regular.TwoSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Syntax.Grades.Example.Traces.Rigid.Regular.TwoSided Op n code name name-code code-name running
  using (two-sided; operation)

open import DenotationalSemantics.Model.World.History ℕᵀ Op two-sided operation public
