------------------------------------------------------------------------
-- The non-rigid banked trace grades over the non-negative rationals  --
-- as rigid finite-expression grades (`Traces.Banked.ExactGrades`).   --
--                                                                    --
-- The traces are ordered by the codes of their operations, and the   --
-- costs are the ends of the running times: an allowance charges an   --
-- operation `costʰⁱ`, a guarantee credits it `costˡᵒ`.               --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.Traces.TimedRegex.Finite.NonRigid
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

import Data.Fin.Base as Fin
import Data.Fin.Properties as Fin
open import Relation.Binary.Definitions using (DecidableEquality; Trichotomous; tri<; tri≈; tri>)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Util.NonNegativeRational using (#_; _≤?_)
open import Grades.Durations.Monus ℚ≥0ᵀ using (0ᴰ; _<ᴰ_)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

-- operations compared by their codes

_≟ₒ_ : DecidableEquality Op
o ≟ₒ o′ with code o Fin.≟ code o′
... | yes e = yes (code-injective e)
... | no ¬e = no λ { refl → ¬e refl }

_<ᵒ_ : Op → Op → Set
o <ᵒ o′ = code o Fin.< code o′

<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_
<ᵒ-cmp o o′ with Fin.<-cmp (code o) (code o′)
... | tri< a ¬b ¬c = tri< a (λ e → ¬b (cong code e)) ¬c
... | tri≈ ¬a b ¬c = tri≈ ¬a (code-injective b) ¬c
... | tri> ¬a ¬b c = tri> ¬a (λ e → ¬b (cong code e)) c

<ᵒ-trans : ∀ {o o′ o″} → o <ᵒ o′ → o′ <ᵒ o″ → o <ᵒ o″
<ᵒ-trans = Fin.<-trans

open import Grades.Examples.Traces.Banked.ExactGrades
  ℚ≥0ᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans n code code-injective name code-name running
  ℚ≥0-dense (# 1) one-pos public
