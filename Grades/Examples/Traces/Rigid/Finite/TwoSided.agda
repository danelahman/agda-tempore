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

module Grades.Examples.Traces.Rigid.Finite.TwoSided
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

two-sided : Grade ℚ≥0ᴰ
Grade.Carrier         two-sided = I.Carrier
Grade._·_             two-sided = I._·_
Grade.u               two-sided = I.u
Grade._≾_             two-sided = I._≾_
Grade.⊤               two-sided = I.⊤
Grade._⊔_             two-sided = I._⊔_
Grade.of-dur          two-sided = I.of-dur
Grade.·-identityˡ     two-sided = I.·-identityˡ
Grade.·-identityʳ     two-sided = I.·-identityʳ
Grade.·-assoc         two-sided = I.·-assoc
Grade.≾-refl          two-sided {c} = I.≾-refl {c}
Grade.≾-trans         two-sided {c} {d} {e} = I.≾-trans {c} {d} {e}
Grade.≾-irrelevant    two-sided {c} {d} = I.≾-irrelevant {c} {d}
Grade._≾?_            two-sided = I._≾?_
Grade.≾-⊤             two-sided = I.≾-⊤
Grade.⊔-ubˡ           two-sided = I.⊔-ubˡ
Grade.⊔-ubʳ           two-sided = I.⊔-ubʳ
Grade.⊔-lub           two-sided {c} {d} {e} = I.⊔-lub {c} {d} {e}
Grade.·-monoˡ-≾       two-sided {c} {d} {e} = I.·-monoˡ-≾ {c} {d} {e}
Grade.·-monoʳ-≾       two-sided {c} {d} {e} = I.·-monoʳ-≾ {c} {d} {e}
Grade.·-distribˡ-⊔-≾  two-sided = I.·-distribˡ-⊔-≾
Grade.·-distribʳ-⊔-≾  two-sided = I.·-distribʳ-⊔-≾
Grade.≾-zero-productˡ two-sided {c} {d} = I.≾-zero-productˡ {c} {d}
Grade.≾-zero-productʳ two-sided {c} {d} = I.≾-zero-productʳ {c} {d}
Grade.of-dur-zero     two-sided = I.of-dur-zero
Grade.of-dur-plus     two-sided {τ} {τ′} = I.of-dur-plus {τ} {τ′}
