------------------------------------------------------------------------
-- Typed example computations at the flow-sensitive levels.           --
--                                                                    --
-- Effect grades and resource grades are both a level touched and the --
-- level each sink is written at, the sinks being local memory and    --
-- the radio. Reading the sensor touches `High`; storing writes the   --
-- memory and transmitting writes the radio, each at `Low`, raised to --
-- whatever was touched before. Idling touches nothing.               --
--                                                                    --
-- A policy that keeps the radio at `Low` admits transmitting a       --
-- constant and then reading, and refuses transmitting the reading:   --
-- the order of the two decides the level the radio is written at. A  --
-- box graded `(Low , every sink at High)` is a public channel,       --
-- claimable while nothing `High` has been touched since boxing,      --
-- whatever is written meanwhile.                                     --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order:  --
-- a reading survives idling and goes stale after an operation, and a --
-- handler clause may discard its continuation, the unit being least. --
--                                                                    --
-- Every side condition is discharged by the decision procedure of    --
-- the grade (`decided`, `check`), and every refutation by it         --
-- (`refuted`).                                                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.SemiDirect.FlowLevels where

open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Syntax.Durations.Nat using (ℕᴰ)
open import Syntax.Grades using (Grade)
open import Syntax.Grades.Indexed using (ℕ-names; module Maps)
open import Syntax.Grades.Example.SecurityLevel using (LowHigh; Low; High; Low⊑)
open import Syntax.Grades.Example.SemiDirect.FlowLevels using (two-point-flow-levels)
open import Syntax.Grades.Example.Worked.Operations using (Op; read; write; send)
open import Syntax.Grades.Example.System.Identity using (noWitnesses)

import Data.List.Base as L

open Maps ℕ-names using (Map; _∣_; pointwise⁺)

flow : Grade ℕᴰ
flow = two-point-flow-levels

memory radio : ℕ
memory = 0
radio  = 1

-- a level touched, with no output

touches : LowHigh → Grade.Carrier flow
touches l = l , (nothing ∣ L.[])

-- a sink written at a level, touching nothing above `Low`

writes : ℕ → LowHigh → Grade.Carrier flow
writes s l = Low , (nothing ∣ ((s , just l) L.∷ L.[]))

------------------------------------------------------------------------
-- The operations

opTime : Op → Grade.Carrier flow
opTime read  = touches High
opTime write = writes memory Low
opTime send  = writes radio Low

open import Syntax.Grades.Example.Worked.Typing.Core flow opTime noWitnesses

decided : ∀ {c d : R} {p : True (c ≾ᵣ? d)} → c ≾ᵣ d
decided {p = p} = toWitness p

refuted : (c d : R) {p : False (c ≾ᵣ? d)} → ¬ (c ≾ᵣ d)
refuted c d {p} = toWitnessFalse p

check : ∀ {Γ A ε} (ε' : E) {p : True (ε ≾ₑ? ε')} → Γ ⊢C⦂ A ‼ ε → Γ ⊢C⦂ A ‼ ε'
check ε' {p} M = coerce (toWitness p) M

------------------------------------------------------------------------
-- A policy: anything may be touched and stored, the radio only at `Low`

radio-low : E
radio-low = High , (just High ∣ ((radio , just Low) L.∷ L.[]))

-- transmitting a constant before reading keeps it

announce-then-sample : [] ⊢C⦂ Reading ‼ radio-low
announce-then-sample =
  check radio-low
    (perform send (const 0)          -- ⟨ opTime send ⟩ ∷ Unit
      (perform read ⋆                -- ⟨ opTime read ⟩ ∷ Reading
        (return here)))

-- storing the reading keeps it too: memory may be written at `High`

sample-then-store : [] ⊢C⦂ Unit ‼ radio-low
sample-then-store =
  check radio-low
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (perform write here            -- ⟨ opTime write ⟩ ∷ Unit
        (return ⋆)))

-- transmitting the reading is a program, graded by what it does

relaying : [] ⊢C⦂ Unit ‼ (opTime read ·ₑ (opTime send ·ₑ uₑ))
relaying =
  perform read ⋆                     -- ⟨ opTime read ⟩ ∷ Reading
    (perform send here               -- ⟨ opTime send ⟩ ∷ Unit
      (return ⋆))

-- and that grade writes the radio at `High`, breaking the policy

relaying-refused : ¬ (opTime read ·ₑ (opTime send ·ₑ uₑ) ≾ₑ radio-low)
relaying-refused = refuted (opTime read ·ₑ (opTime send ·ₑ uₑ)) radio-low

------------------------------------------------------------------------
-- Readings survive idling, not an operation

idle-then-store : [] ⊢C⦂ Unit ‼ radio-low
idle-then-store =
  check radio-low
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (delay 5                       -- ⟨ uᵣ ⟩
        (perform write (fresh-var decided (Tl-⟨⟩ Hd))
                                     -- ⟨ opTime write ⟩ ∷ Unit
          (return ⋆))))

stale-after-storing : ¬ (uᵣ ·ᵣ opTime write ≾ᵣ uᵣ)
stale-after-storing = refuted (uᵣ ·ᵣ opTime write) uᵣ

------------------------------------------------------------------------
-- Unboxing: a public channel, claimable while nothing `High` has been
-- touched

channel : R
channel = Low , (just High ∣ L.[])

-- storing between boxing and claiming leaves the channel public

store-then-claim : [] ⊢C⦂ Unit ‼ radio-low
store-then-claim =
  check radio-low
    (box channel (const 7)           -- ∷ [ channel ] Reading
      (perform write (const 1)       -- ⟨ opTime write ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ Hd)) decided (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

-- reading the sensor in between closes it

claim-after-reading : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ channel)
claim-after-reading = refuted (uᵣ ·ᵣ opTime read) channel

------------------------------------------------------------------------
-- Effect handling: the unit is least, so a clause may discard its
-- continuation

nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits op ε'' = Low⊑ , pointwise⁺ _ (λ _ → tt)

-- the clauses discard the transmission, but `handle` is graded by the
-- handled computation, so the radio is still written at `High`

suppressed : [] ⊢C⦂ Unit ‼ ((opTime read ·ₑ (opTime send ·ₑ uₑ)) ·ₑ uₑ)
suppressed =
  handle perform read ⋆ (perform send here (return ⋆))
    `with discarding {[]} nothing-fits
    `in                              -- ⟨ opTime read · opTime send ⟩ ∷ Unit
      (return ⋆)
