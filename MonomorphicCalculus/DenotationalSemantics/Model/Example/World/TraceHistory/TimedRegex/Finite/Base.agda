------------------------------------------------------------------------
-- Trace-history frames for the rigid timed finite-expression grades: --
-- what the upper-bound, lower-bound and interval frames share.       --
--                                                                    --
-- A history is a timed trace, read in a grade by `World.History`. An --
-- operation is read as the letter `‵ o`, one run of it for a time    --
-- its running-time interval admits. A trace's events are the run it  --
-- records (`Exact.Hull`).                                            --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
import Grades.Traces.RunningTimes as RunningTimes

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.TimedRegex.Finite.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Bool.Base using (true; false) renaming (T to IsTrue)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (⁅_⁆)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Util.NonNegativeRational using (#_; _≤?_)
open import Grades.Durations.Monus ℚ≥0ᵀ using (0ᴰ; _<ᴰ_)

open import Grades.Examples.Traces.TimedRegex.Finite.Base Op n code name name-code code-name running
  using (Instance; Proper′; ⌜_⌝; ‵_)

open import Grades.Traces.Base ℚ≥0ᵀ Op
  using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; ∣_∣⁺)

code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

private
  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Grades.Exact.Finite ℚ≥0ᵀ Op n code code-injective name code-name running
  ℚ≥0-dense (# 1) one-pos using (members; nonEmpty)

open import Grades.Exact.Hull ℚ≥0ᵀ Op n code code-injective running
  using (Run; perform) renaming (delay to wait) public

------------------------------------------------------------------------
-- The grade of an operation

private
  nonEmpty-map : ∀ {A B : Set} (f : A → B) (xs : List A)
               → IsTrue (nonEmpty xs) → IsTrue (nonEmpty (map f xs))
  nonEmpty-map f (_ ∷ _) _ = tt

  members-⁅⁆ : ∀ {m} (c : Fin m) → IsTrue (nonEmpty (members ⁅ c ⁆))
  members-⁅⁆ zero    = tt
  members-⁅⁆ (suc c) = nonEmpty-map suc _ (members-⁅⁆ c)

‵ᵍ : ∀ {s} → Op → Proper′ s
‵ᵍ o = ⌜ ‵ o ⌝ {nonEmpty-map _ _ (members-⁅⁆ (code o))}

------------------------------------------------------------------------
-- The run a trace records

events  : Trace → Run
events⁻ : Trace⁻ → Run

events ε               = []
events (operation o s) = perform o ∷ events s
events (delay d s)     = wait ∣ d ∣⁺ ∷ events⁻ s

events⁻ ε⁻               = []
events⁻ (operation⁻ o s) = perform o ∷ events s
