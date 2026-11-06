------------------------------------------------------------------------
-- Trace-history frames for the timed regex grades in whole steps:    --
-- what the upper-bound, lower-bound and interval frames share.       --
--                                                                    --
-- A history is a timed trace, read in a grade by `World.History`. An --
-- operation is read as the literal of `‵ o`, one run of it for a     --
-- time its running-time interval admits (`rt-inhabited⁺`).           --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)
import Grades.Traces.RunningTimes as RunningTimes

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Nat.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)

open RunningTimes.RunningTimes running using (rt-inhabited⁺)

open import Grades.Examples.Traces.TimedRegex.Nat.Base Op n code name name-code code-name running
  using (Closed; ⌜_⌝′; ‵_; op; upper)

-- the grade of an operation

‵ᵍ : Op → Closed
‵ᵍ o = ⌜ ‵_ {upper} o ⌝′ (op o (proj₁ (rt-inhabited⁺ o)) ∷ [] ,
                     o , proj₁ (rt-inhabited⁺ o) , x∈⁅x⁆ (code o) , proj₂ (rt-inhabited⁺ o) , refl)
