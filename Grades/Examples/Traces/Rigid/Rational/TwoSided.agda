------------------------------------------------------------------------
-- Rigid timed regular-expression grades over the non-negative       --
-- rationals, as intervals.                                           --
--                                                                    --
-- A grade `[ L , U ]` pairs a lower bound `L` with an upper bound    --
-- `U` that some exact run fits (`Exact.Regular.Interval`), compared  --
-- componentwise. A delay is graded by the waits of at least and at   --
-- most its length: together, a wait of exactly it. A literal         --
-- `[ L , U ]` is decided consistent (`Exact.Joint.Decide`);          --
-- `[ L , U ]⟨ r ⟩` names a common run `r` instead.                   --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ; ℚ≥0-dense)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.Traces.Rigid.Rational.TwoSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Durations.Monus ℚ≥0ᵀ using (0ᴰ; _<ᴰ_)
open import Util.NonNegativeRational using (#_; _≤?_)
open import Grades.Exact.Grid.NonNegativeRational using (ℚ≥0-commensurable)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Grades.Exact.Regular.Interval ℚ≥0ᵀ Op n code code-injective name code-name
  running ℚ≥0-dense (# 1) one-pos ℚ≥0-commensurable public
open import Grades.Exact.Regular.Grades ℚ≥0ᵀ Op n code code-injective name code-name
  running ℚ≥0-dense (# 1) one-pos ℚ≥0-commensurable using (lowerʰ; upperʰ)

two-sided : Grade ℚ≥0ᴰ
two-sided = intervalᵍ

two-sidedʰ : GradeHints two-sided
two-sidedʰ = intervalʰ lowerʰ upperʰ
