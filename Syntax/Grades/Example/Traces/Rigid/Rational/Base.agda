------------------------------------------------------------------------
-- Rigid timed regular-expression grades over the non-negative       --
-- rationals: what the right-, left- and two-sided grades share.      --
--                                                                    --
-- Grades are one-sided expressions with iteration                    --
-- (`Exact.Regular.Grades`), written with `⌜_⌝`, whose side condition --
-- -- at least one word -- is computed. A comparison is decided by    --
-- the automaton of the reader, over the unit the rationals of the    --
-- two expressions share; `holds` reads the decision as a Boolean, so --
-- that a comparison is checked by evaluation.                        --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Rational.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes; toWitnessFalse)

open import Syntax.Grades.Example.Time.Dense.NonNegativeRational using (#_; _≤?_)
open import Syntax.Durations.Monus ℚ≥0ᵀ using (Carrier; 0ᴰ; _<ᴰ_)
open import Syntax.Grades.Exact.Grid.NonNegativeRational using (ℚ≥0-commensurable)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Syntax.Grades.Exact.Expression ℚ≥0ᵀ Op n code code-injective running public
open import Syntax.Grades.Exact.Regular.Grades ℚ≥0ᵀ Op n code code-injective name code-name running
  ℚ≥0-dense (# 1) one-pos ℚ≥0-commensurable public
open import Syntax.Grades.Exact.Base ℚ≥0ᵀ Op n code code-injective public using (OpSet)

------------------------------------------------------------------------
-- Comparisons decided by evaluation

holds : ∀ {s} → Proper′ s → Proper′ s → Bool
holds c d = isYes (c ≾ᵉ? d)

holds′ : ∀ {s} (c d : Proper′ s) → holds c d ≡ true → c ≾ᵉ d
holds′ c d e with c ≾ᵉ? d
... | yes p = p

fails′ : ∀ {s} (c d : Proper′ s) → holds c d ≡ false → ¬ (c ≾ᵉ d)
fails′ c d e with c ≾ᵉ? d
... | no ¬p = ¬p
