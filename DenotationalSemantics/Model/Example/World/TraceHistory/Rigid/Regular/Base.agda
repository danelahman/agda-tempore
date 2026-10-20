------------------------------------------------------------------------
-- Trace-history frames for the rigid timed regular grades in whole   --
-- steps: what the right-, left- and two-sided frames share.          --
--                                                                    --
-- A history is a timed trace, read in a grade by `World.History`. An --
-- operation is read as the literal of `‵ o`, one run of it for a     --
-- time its running-time interval admits (`rt-inhabited⁺`).           --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Regular.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)

open RunningTimes.RunningTimes running using (rt-inhabited⁺)

open import Syntax.Grades.Example.Traces.Rigid.Regular.Base Op n code name name-code code-name running
  using (Closed; ⌜_⌝′; ‵_; op; upper)

-- the grade of an operation

‵ᵍ : Op → Closed
‵ᵍ o = ⌜ ‵_ {upper} o ⌝′ (op o (proj₁ (rt-inhabited⁺ o)) ∷ [] ,
                     o , proj₁ (rt-inhabited⁺ o) , x∈⁅x⁆ (code o) , proj₂ (rt-inhabited⁺ o) , refl)
