------------------------------------------------------------------------
-- Rigid timed finite-expression grades over the non-negative         --
-- rationals, as intervals.                                           --
--                                                                    --
-- A grade `[ L , U ]` pairs a lower bound `L` with an upper bound    --
-- `U` that some exact run fits (`Exact.Finite.Interval`), compared   --
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

module Grades.Examples.Traces.TimedRegex.Finite.Interval
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Grades.Base using (Grade)
open import Grades.Durations.Monus ℚ≥0ᵀ using (0ᴰ; _<ᴰ_)
open import Util.NonNegativeRational using (#_; _≤?_)
open import Grades.Exact.Grid.NonNegativeRational using (ℚ≥0-commensurable)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Grades.Exact.Finite.Interval ℚ≥0ᵀ Op n code code-injective name code-name
  running ℚ≥0-dense (# 1) one-pos public
open Decided ℚ≥0-commensurable public

-- `intervalᵍ` by copatterns, so that the grade is compared by name and
-- not as a record value

private
  module I = Grade intervalᵍ

interval : Grade ℚ≥0ᴰ
Grade.Carrier         interval = I.Carrier
Grade._·_             interval = I._·_
Grade.𝟏               interval = I.𝟏
Grade._≾_             interval = I._≾_
Grade.⊤               interval = I.⊤
Grade._⊔_             interval = I._⊔_
Grade.ι               interval = I.ι
Grade.·-identityˡ     interval = I.·-identityˡ
Grade.·-identityʳ     interval = I.·-identityʳ
Grade.·-assoc         interval = I.·-assoc
Grade.≾-refl          interval {c} = I.≾-refl {c}
Grade.≾-trans         interval {c} {d} {e} = I.≾-trans {c} {d} {e}
Grade.≾-irrelevant    interval {c} {d} = I.≾-irrelevant {c} {d}
Grade._≾?_            interval = I._≾?_
Grade.≾-⊤             interval = I.≾-⊤
Grade.⊔-ubˡ           interval = I.⊔-ubˡ
Grade.⊔-ubʳ           interval = I.⊔-ubʳ
Grade.⊔-lub           interval {c} {d} {e} = I.⊔-lub {c} {d} {e}
Grade.·-monoˡ-≾       interval {c} {d} {e} = I.·-monoˡ-≾ {c} {d} {e}
Grade.·-monoʳ-≾       interval {c} {d} {e} = I.·-monoʳ-≾ {c} {d} {e}
Grade.·-distribˡ-⊔-≾  interval = I.·-distribˡ-⊔-≾
Grade.·-distribʳ-⊔-≾  interval = I.·-distribʳ-⊔-≾
Grade.≾-zero-productˡ interval {c} {d} = I.≾-zero-productˡ {c} {d}
Grade.≾-zero-productʳ interval {c} {d} = I.≾-zero-productʳ {c} {d}
Grade.ι-zero          interval = I.ι-zero
Grade.ι-plus          interval {τ} {τ′} = I.ι-plus {τ} {τ′}
