------------------------------------------------------------------------
-- Typed example computations at the mode-switch costs.               --
--                                                                    --
-- Effect grades and resource grades are both mode-switch costs over  --
-- two modes of the node, `Idle` (mode 0) and `Radio` (mode 1), the   --
-- radio on. Reading works in every mode and keeps it; storing works  --
-- only when idle, the memory and the radio sharing a bus; and        --
-- transmitting switches the radio on from `Idle`, at cost 1, or      --
-- transmits with it on, at no cost. From any other mode an operation --
-- gets stuck.                                                        --
--                                                                    --
-- A policy "the radio switched on at most once, never stuck from     --
-- `Idle` or `Radio`" admits two transmissions and refuses storing    --
-- after a transmission, which gets stuck. A box graded "at most one  --
-- switch since boxing" is claimable after a transmission.            --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order:  --
-- a reading survives reading and idling and goes stale after a       --
-- store, which gets stuck from `Radio`; and the unit is not least,   --
-- so a handler clause cannot discard its continuation.               --
--                                                                    --
-- Every side condition is discharged by the decision procedure of    --
-- the grade (`decided`, `check`), and every refutation by it         --
-- (`refuted`).                                                       --
------------------------------------------------------------------------

module ClosedCalculus.Examples.Typing.SemiDirect.ModeSwitchCosts where

open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

import Data.List.Base as L

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Examples.SemiDirect.ModeSwitchCosts
  renaming (decided to grade)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)

Idle Radio : Point
Idle  = ⟨ 0 ⟩
Radio = ⟨ 1 ⟩

------------------------------------------------------------------------
-- The operations

opTime : Op → Grade.Carrier (mode-switch-costs {ℕᴰ})
opTime read  = Grade.u (mode-switch-costs {ℕᴰ})
opTime write = grade (listing ((Idle , Idle , cost 0) L.∷ L.[]))
opTime send  = grade (listing ((Idle , Radio , cost 1) L.∷ (Radio , Radio , cost 0) L.∷ L.[]))

open import ClosedCalculus.Examples.Typing.Core (mode-switch-costs {ℕᴰ}) opTime

decided : (c d : R) {p : True (c ≾ᵣ? d)} → c ≾ᵣ d
decided c d {p} = toWitness p

refuted : (c d : R) {p : False (c ≾ᵣ? d)} → ¬ (c ≾ᵣ d)
refuted c d {p} = toWitnessFalse p

check : ∀ {Γ A ε} (ε' : E) {p : True (ε ≾ₑ? ε')} → Γ ⊢C⦂ A ‼ ε → Γ ⊢C⦂ A ‼ ε'
check ε' {p} M = coerce (toWitness p) M

------------------------------------------------------------------------
-- A policy: the radio switched on at most once

one-switch : E
one-switch = grade (listing ((Idle , Radio , cost 1) L.∷ (Radio , Radio , cost 0) L.∷ L.[]))

two-transmissions : [] ⊢C⦂ Unit ‼ one-switch
two-transmissions =
  check one-switch
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (perform send here             -- ⟨ opTime send ⟩ ∷ Unit
        (perform read ⋆              -- ⟨ opTime read ⟩ ∷ Reading
          (perform send here         -- ⟨ opTime send ⟩ ∷ Unit
            (return ⋆)))))

-- storing after a transmission gets stuck

store-after-transmitting-refused : ¬ (opTime send ·ₑ opTime write ≾ₑ one-switch)
store-after-transmitting-refused = refuted (opTime send ·ₑ opTime write) one-switch

------------------------------------------------------------------------
-- Readings survive reading and idling, not a store

sample-idle-sample-store : [] ⊢C⦂ Unit ‼ opTime write
sample-idle-sample-store =
  check (opTime write)
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (delay 4                       -- ⟨ uᵣ ⟩
        (perform read ⋆              -- ⟨ opTime read ⟩ ∷ Reading
          (perform write (fresh-var (decided (uᵣ ·ᵣ of-durʳ 4 ·ᵣ opTime read) uᵣ)
                                      (Tl-∷ (Tl-⟨⟩ (Tl-⟨⟩ Hd))))
                                     -- ⟨ opTime write ⟩ ∷ Unit
            (return ⋆)))))

stale-after-storing : ¬ (uᵣ ·ᵣ opTime write ≾ᵣ uᵣ)
stale-after-storing = refuted (uᵣ ·ᵣ opTime write) uᵣ

------------------------------------------------------------------------
-- Unboxing: claimable after at most one switch, the modes not named
-- kept or stuck

at-most-one-switch : R
at-most-one-switch =
  grade (listing ((Idle , Idle , cost 0) L.∷ (Idle , Radio , cost 1) L.∷ (Radio , Radio , cost 0)
               L.∷ (⋆ , ⋆ , cost 0) L.∷ (⋆ , ✗ , cost 0) L.∷ L.[]))

claim-after-a-transmission : [] ⊢C⦂ Unit ‼ one-switch
claim-after-a-transmission =
  check one-switch
    (box at-most-one-switch (const 7)
                                     -- ∷ [ at-most-one-switch ] Reading
      (perform send (const 1)        -- ⟨ opTime send ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (decided (uᵣ ·ᵣ opTime send) at-most-one-switch) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

-- a store before the claim may get stuck

claim-after-a-store : ¬ (uᵣ ·ᵣ opTime write ≾ᵣ at-most-one-switch)
claim-after-a-store = refuted (uᵣ ·ᵣ opTime write) at-most-one-switch

------------------------------------------------------------------------
-- Effect handling: the unit is not least, so no clause discards a
-- transmission's continuation

cannot-discard : ¬ (uₑ ≾ₑ opTime send ·ₑ uₑ)
cannot-discard = refuted uₑ (opTime send ·ₑ uₑ)
