------------------------------------------------------------------------
-- Typed example computations at the rigid timed interval grade.      --
--                                                                    --
-- A grade `[ L , U ]` pairs a guarantee with a bound, each a regular --
-- expression over interval letters, that a common run fits. The      --
-- guarantee below demands a reading, then an undisturbed wait of at  --
-- least five steps, with anything before and after; the bound allows --
-- a reading and at most twelve steps of anything after it. A box at  --
-- this grade may be unboxed after a reading and a wait of five       --
-- steps; after a reading and two transmissions instead it may not,   --
-- the transmissions filling the wait the guarantee demands, though   --
-- they stay within the bound and within a guarantee asking only for  --
-- five steps of anything.                                            --
--                                                                    --
-- Reading takes one step, writing two or three, sending four to six. --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Traces.Rigid.Regular.TwoSided where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.Product using (_×_; _,_)
open import Grades.Base using (module Grade)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)
open import Grades.Durations.Intervals ℕᵀ using (⟪_,_⟫; fin; ⁻; ⁺; _⊑?_; 0⁺)
  renaming (_∣_ to _∣ᶜ_)
open import Grades.Traces.RunningTimes ℕᵀ using (RunningTimes; Bounded)
open import Grades.Durations.Intervals.Dense ℕᵀ using (_∈ⁱ?_)

open import Grades.Examples.Worked.Operations using (Op; read; write; send)

------------------------------------------------------------------------
-- The operations, coded, and their running times

code : Op → Fin 3
code read  = zero
code write = suc zero
code send  = suc (suc zero)

name : Fin 3 → Op
name zero             = read
name (suc zero)       = write
name (suc (suc zero)) = send

name-code : ∀ o → name (code o) ≡ o
name-code read  = refl
name-code write = refl
name-code send  = refl

code-name : ∀ c → code (name c) ≡ c
code-name zero             = refl
code-name (suc zero)       = refl
code-name (suc (suc zero)) = refl

running : RunningTimes Op
running = record
  { rt          = λ { read  → ⟪ 1 ∣ᶜ ⁻ , fin (1 ∣ᶜ ⁺) ⟫
                    ; write → ⟪ 2 ∣ᶜ ⁻ , fin (3 ∣ᶜ ⁺) ⟫
                    ; send  → ⟪ 4 ∣ᶜ ⁻ , fin (6 ∣ᶜ ⁺) ⟫ }
  ; rt-bounded  = λ { read → Bounded.fin (1 ∣ᶜ ⁺) ; write → Bounded.fin (3 ∣ᶜ ⁺)
                    ; send → Bounded.fin (6 ∣ᶜ ⁺) }
  ; rt-positive = λ { read  → toWitness {a? = 0⁺ ⊑? (1 ∣ᶜ ⁻)} _
                    ; write → toWitness {a? = 0⁺ ⊑? (2 ∣ᶜ ⁻)} _
                    ; send  → toWitness {a? = 0⁺ ⊑? (4 ∣ᶜ ⁻)} _ }
  ; rt-inhabited = λ { read  → 1 , toWitness {a? = 1 ∈ⁱ? ⟪ 1 ∣ᶜ ⁻ , fin (1 ∣ᶜ ⁺) ⟫} _
                     ; write → 2 , toWitness {a? = 2 ∈ⁱ? ⟪ 2 ∣ᶜ ⁻ , fin (3 ∣ᶜ ⁺) ⟫} _
                     ; send  → 4 , toWitness {a? = 4 ∈ⁱ? ⟪ 4 ∣ᶜ ⁻ , fin (6 ∣ᶜ ⁺) ⟫} _ }
  }

import Grades.Examples.Traces.Rigid.Regular.LeftSided Op 3 code name name-code code-name running as L
import Grades.Examples.Traces.Rigid.Regular.RightSided Op 3 code name name-code code-name running as U
open import Grades.Examples.Traces.Rigid.Regular.TwoSided Op 3 code name name-code code-name running
  using (two-sided; operation; Consistent; consistent?; [_,_]; [_,_]⟨_⟩; perform; delay)

open L using (Closed; ‵_; _·_; ≥_; idle_; upper; lower; holds′; fails′)
open U using (≤_)

------------------------------------------------------------------------
-- The operations, graded by the operation at both endpoints

opTime : Op → Grade.Carrier two-sided
opTime = operation

open import MonomorphicCalculus.Examples.Typing.Core two-sided opTime

------------------------------------------------------------------------
-- The contracts

settling settling-busy : Closed
settling      = L.⌜ ≥ 0 · ‵ read · idle ≥ 5 · ≥ 0 ⌝
settling-busy = L.⌜ ≥ 0 · ‵ read · ≥ 5 · ≥ 0 ⌝

within-twelve : Closed
within-twelve = U.⌜ ‵ read · ≤ 12 ⌝

contract contract-busy : R
contract      = [ settling      , within-twelve ]
contract-busy = [ settling-busy , within-twelve ]⟨ perform read ∷ᴸ delay 5 ∷ᴸ []ᴸ ⟩

-- a wait of at least five steps within at most two: no run fits both

waiting brief : Closed
waiting = L.⌜ idle ≥ 5 ⌝
brief   = U.⌜ ≤ 2 ⌝

impatient : ¬ Consistent (waiting , brief)
impatient = toWitnessFalse {a? = consistent? (waiting , brief)} _

------------------------------------------------------------------------
-- A box at the contract, opened after the wait

settled : [] ⊢ᶜ⦂ unit ! _
settled =
  box contract (const reading 42) -- ∷ [ contract ] Reading
    (perform read ⋆               -- ⟨ opTime read ⟩ ∷ Reading
      (delay 5                    -- ⟨ ι 5 ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) (holds′ refl , holds′ refl) (<:ᵛ-refl _)
                             -- ∷ Reading
          (perform write here (return ⋆)))))

-- transmitting twice in place of waiting fills the wait the contract
-- demands: the box cannot be opened

stirred-run : R
stirred-run = 𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime send ·ᵣ opTime send

stirred : ¬ (stirred-run ≾ᵣ contract)
stirred (p , _) = fails′ refl p

-- the transmissions stay within the bound, and give the five steps of
-- a guarantee that does not ask for an undisturbed wait

stirred-busy : stirred-run ≾ᵣ contract-busy
stirred-busy = holds′ refl , holds′ refl
