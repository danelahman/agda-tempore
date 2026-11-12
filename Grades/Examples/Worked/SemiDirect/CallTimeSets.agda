------------------------------------------------------------------------
-- Worked instances of the call-time sets, at the sensor node.        --
--                                                                    --
-- The operations are the names 0, 1, 2 (`read`, `write`, `send`). A  --
-- transmission taking one step is `(1 , send at {0})`: it happens at --
-- its start. Two of them in a row take two steps and transmit at     --
-- times 0 and 1; idling two steps first shifts the transmission to   --
-- time 2. A call-time set that allows transmissions only at times 2  --
-- to 4 admits the second, and refuses transmitting before idling two --
-- steps. The unit, taking no time and doing nothing, is not least: a --
-- grade that takes at least one step is not above it. Every ordering --
-- is established by the decision procedure of the grade, and every   --
-- computation by reduction.                                          --
------------------------------------------------------------------------

module Grades.Examples.Worked.SemiDirect.CallTimeSets where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import Grades.Examples.SemiDirect.CallTimeSets
  using (call-time-sets; durations; Durations; Times; ⟪_⟫ₜ; _∪ₜ_; ∅ₜ)

open Maps ℕ-names using (Map; _∣_)
open Grade call-time-sets using (Carrier; _≾_; _≾?_; _≃_; _≃?_; _·_; _⊔_; 𝟏)
open Grade durations using (ι) renaming (_⊔_ to _⊔ᴰ_)

name : Op → ℕ
name read  = 0
name write = 1
name send  = 2

-- the durations from `n` to `n + k`

durations-between : ℕ → ℕ → Durations
durations-between n 0       = ι n
durations-between n (suc k) = durations-between n k ⊔ᴰ ι (n + suc k)

-- the times from `n` to `n + k`

times-between : ℕ → ℕ → Times
times-between n 0       = ⟪ n ⟫ₜ
times-between n (suc k) = times-between n k ∪ₜ ⟪ n + suc k ⟫ₜ

-- taking `T`, performing nothing

takes : Durations → Carrier
takes T = T , (∅ₜ ∣ [])

-- taking `T`, performing `o` only at times `E`

at : Durations → Op → Times → Carrier
at T o E = T , (∅ₜ ∣ ((name o , E) ∷ []))

holds : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
holds c d {p} = toWitness p

fails : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
fails c d {p} = toWitnessFalse p

equal : (c d : Carrier) {p : True (c ≃? d)} → c ≃ d
equal c d {p} = toWitness p

-- a transmission, one step long, at its start

transmit : Carrier
transmit = at (ι 1) send ⟪ 0 ⟫ₜ

-- two in a row transmit at times 0 and 1, and take two steps

twice : transmit · transmit ≃ at (ι 2) send (times-between 0 1)
twice = equal (transmit · transmit) (at (ι 2) send (times-between 0 1))

-- idling first shifts the transmission

idle-first : takes (ι 2) · transmit ≃ at (ι 3) send ⟪ 2 ⟫ₜ
idle-first = equal (takes (ι 2) · transmit) (at (ι 3) send ⟪ 2 ⟫ₜ)

-- a call-time set: two to six steps, transmitting only between times 2
-- and 4

slot : Carrier
slot = at (durations-between 2 4) send (times-between 2 2)

late-ok : takes (ι 2) · transmit ≾ slot
late-ok = holds (takes (ι 2) · transmit) slot

early-refused : ¬ (transmit · takes (ι 2) ≾ slot)
early-refused = fails (transmit · takes (ι 2)) slot

-- so the product does not commute

not-commutative : ¬ (takes (ι 2) · transmit ≾ transmit · takes (ι 2))
not-commutative = fails (takes (ι 2) · transmit) (transmit · takes (ι 2))

-- a branch that idles one or two steps first transmits at time 1 or 2

branching : (takes (ι 1) ⊔ takes (ι 2)) · transmit
          ≃ at (durations-between 2 1) send (times-between 1 1)
branching = equal ((takes (ι 1) ⊔ takes (ι 2)) · transmit) (at (durations-between 2 1) send (times-between 1 1))

-- the unit is not least

unit-not-least : ¬ (𝟏 ≾ takes (ι 1))
unit-not-least = fails 𝟏 (takes (ι 1))
