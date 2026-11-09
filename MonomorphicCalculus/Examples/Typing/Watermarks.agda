------------------------------------------------------------------------
-- Typed computations at the watermark grades                         --
--                                                                    --
-- The grade                                                          --
--   Effect grades and resource grades are both the trough, net       --
--   change and peak of one resource, the slots of the node's local   --
--   memory: storing a reading occupies a slot, `(0 , [1 , 1] , 1)`,  --
--   and transmitting one frees it, `(-1 , [-1 , -1] , 0)`; reading   --
--   and idling touch no slot.                                        --
--                                                                    --
-- What it shows                                                      --
--   A buffer of one slot, all freed and none freed that was not      --
--   occupied, `(0 , [0 , 0] , 1)`, admits storing and then           --
--   transmitting, and refuses transmitting first and storing twice.  --
--   A box graded `(0 , [0 , 1] , 1)` is claimable while at most one  --
--   slot has been occupied since boxing and none freed beyond.       --
--                                                                    --
--   The two rules that place the unit on opposite sides of the       --
--   order: a reading survives reading and idling and goes stale      --
--   after a store or a transmission, and the unit is not least, so a --
--   handler clause cannot discard its continuation.                  --
--                                                                    --
-- How to read them                                                   --
--   Every side condition is discharged by the decision procedure of  --
--   the grade (`decided`, `check`), and every refutation by it       --
--   (`refuted`).                                                     --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Watermarks where

open import Data.Integer.Base as ℤ using (+_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Examples.Watermarks using (Watermark; one-watermark)
open import Grades.Examples.Worked.Watermarks using (res)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)

------------------------------------------------------------------------
-- The operations

opTime : Op → Watermark
opTime read  = Grade.𝟏 (one-watermark {ℕᴰ})
opTime write = res 0 (+ 1) (+ 1) 1
opTime send  = res 1 (ℤ.- + 1) (ℤ.- + 1) 0

open import MonomorphicCalculus.Examples.Typing.Core (one-watermark {ℕᴰ}) opTime

decided : (c d : R) {p : True (c ≾ᵣ? d)} → c ≾ᵣ d
decided c d {p} = toWitness p

refuted : (c d : R) {p : False (c ≾ᵣ? d)} → ¬ (c ≾ᵣ d)
refuted c d {p} = toWitnessFalse p

check : ∀ {Γ A ε} (ε' : E) {p : True (ε ≾ₑ? ε')} → Γ ⊢ᶜ⦂ A ! ε → Γ ⊢ᶜ⦂ A ! ε'
check ε' {p} M = coerce (toWitness p) M

------------------------------------------------------------------------
-- A buffer of one slot

buffer : E
buffer = res 0 (+ 0) (+ 0) 1

store-then-transmit : [] ⊢ᶜ⦂ unit ! buffer
store-then-transmit =
  check buffer
    (perform read ⋆                     -- ⟨ opTime read ⟩ ∷ Reading
      (perform write here               -- ⟨ opTime write ⟩ ∷ unit
        (perform send (const reading 0) -- ⟨ opTime send ⟩ ∷ unit
          (return ⋆))))

-- transmitting first frees a slot never occupied

transmit-first-refused : ¬ (opTime send ·ₑ opTime write ≾ₑ buffer)
transmit-first-refused = refuted (opTime send ·ₑ opTime write) buffer

-- storing twice occupies two slots

store-twice-refused : ¬ (opTime write ·ₑ opTime write ·ₑ opTime send ·ₑ opTime send ≾ₑ buffer)
store-twice-refused =
  refuted (opTime write ·ₑ opTime write ·ₑ opTime send ·ₑ opTime send) buffer

------------------------------------------------------------------------
-- Readings survive reading and idling, not a store

sample-twice-then-store : [] ⊢ᶜ⦂ unit ! res 0 (+ 1) (+ 1) 1
sample-twice-then-store =
  check (res 0 (+ 1) (+ 1) 1)
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (delay 3                       -- ⟨ 𝟏ᵣ ⟩
        (perform read ⋆              -- ⟨ opTime read ⟩ ∷ Reading
          (perform write (fresh-var (decided (𝟏ᵣ ·ᵣ ιᵣ 3 ·ᵣ opTime read) 𝟏ᵣ)
                                      (Tl-∷ (Tl-⟨⟩ (Tl-⟨⟩ Hd))))
                                     -- ⟨ opTime write ⟩ ∷ unit
            (return ⋆)))))

stale-after-storing : ¬ (𝟏ᵣ ·ᵣ opTime write ≾ᵣ 𝟏ᵣ)
stale-after-storing = refuted (𝟏ᵣ ·ᵣ opTime write) 𝟏ᵣ

------------------------------------------------------------------------
-- Unboxing: claimable while at most one slot is occupied since boxing

one-slot : R
one-slot = res 0 (+ 0) (+ 1) 1

claim-after-a-store : [] ⊢ᶜ⦂ unit ! res 0 (+ 0) (+ 0) 1
claim-after-a-store =
  check (res 0 (+ 0) (+ 0) 1)
    (box one-slot (const reading 7)    -- ∷ [ one-slot ] Reading
      (perform write (const reading 1) -- ⟨ opTime write ⟩ ∷ unit
        (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (decided (𝟏ᵣ ·ᵣ opTime write) one-slot) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

claim-after-two-stores : ¬ (𝟏ᵣ ·ᵣ opTime write ·ᵣ opTime write ≾ᵣ one-slot)
claim-after-two-stores = refuted (𝟏ᵣ ·ᵣ opTime write ·ᵣ opTime write) one-slot

claim-after-a-transmission : ¬ (𝟏ᵣ ·ᵣ opTime send ≾ᵣ one-slot)
claim-after-a-transmission = refuted (𝟏ᵣ ·ᵣ opTime send) one-slot

------------------------------------------------------------------------
-- Effect handling: the unit is not least, so no clause discards a
-- store's continuation

cannot-discard : ¬ (𝟏ₑ ≾ₑ opTime write ·ₑ 𝟏ₑ)
cannot-discard = refuted 𝟏ₑ (opTime write ·ₑ 𝟏ₑ)
