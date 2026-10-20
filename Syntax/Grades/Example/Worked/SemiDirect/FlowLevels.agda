------------------------------------------------------------------------
-- Worked instances of the flow-sensitive levels, at the sensor node. --
--                                                                    --
-- Two sinks, local memory (`memory`, name 0) and the radio (`radio`, --
-- name 1). A grade is the level touched and the level each sink is   --
-- written at. Reading secret data and then transmitting writes the   --
-- radio at `High`; transmitting first and reading afterwards writes  --
-- it at `Low`, so the order of the two matters, and `_·_` does not   --
-- commute. A sink not written stays unwritten, whatever is touched   --
-- before. Every ordering is established by the decision procedure of --
-- the grade, and every computation by reduction.                     --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.SemiDirect.FlowLevels where

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᴰ)
open import Syntax.Grades using (Grade)
open import Syntax.Grades.Indexed using (ℕ-names; module Maps)
open import Syntax.Grades.Example.SecurityLevel using (LowHigh; Low; High)
open import Syntax.Grades.Example.SemiDirect.FlowLevels using (two-point-flow-levels)

open Maps ℕ-names using (Map; _∣_; _!_)

flow : Grade ℕᴰ
flow = two-point-flow-levels

open Grade flow using (Carrier; _≾_; _≾?_; _·_; _⊔_; u; ⊤)

memory radio : ℕ
memory = 0
radio  = 1

-- a level touched, with no output

touches : LowHigh → Carrier
touches l = l , (nothing ∣ [])

-- a sink written at a level, touching nothing above `Low`

writes : ℕ → LowHigh → Carrier
writes s l = Low , (nothing ∣ ((s , just l) ∷ []))

holds : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
holds c d {p} = toWitness p

fails : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
fails c d {p} = toWitnessFalse p

-- read a secret, then transmit

read-then-send : Carrier
read-then-send = touches High · writes radio Low

-- transmit, then read a secret

send-then-read : Carrier
send-then-read = writes radio Low · touches High

-- the radio is written at `High` in the first, at `Low` in the second

radio-raised : proj₂ read-then-send ! radio ≡ just High
radio-raised = refl

radio-kept : proj₂ send-then-read ! radio ≡ just Low
radio-kept = refl

-- both touch `High`

both-high : proj₁ read-then-send ≡ High × proj₁ send-then-read ≡ High
both-high = refl , refl

-- a policy: anything may be touched, but the radio only at `Low`;
-- memory and the other sinks unrestricted

radio-low : Carrier
radio-low = High , (just High ∣ ((radio , just Low) ∷ []))

send-then-read-ok : send-then-read ≾ radio-low
send-then-read-ok = holds send-then-read radio-low

read-then-send-refused : ¬ (read-then-send ≾ radio-low)
read-then-send-refused = fails read-then-send radio-low

-- so the product does not commute

not-commutative : ¬ (read-then-send ≾ send-then-read)
not-commutative = fails read-then-send send-then-read

-- a sink not written stays unwritten after a secret is touched

memory-unwritten : proj₂ read-then-send ! memory ≡ nothing
memory-unwritten = refl

-- writing at `Low` is not "not written"

written-low : ¬ (writes memory Low ≾ u)
written-low = fails (writes memory Low) u

-- the unit is least, and the join takes the higher level at each sink

unit-least : u ≾ read-then-send
unit-least = holds u read-then-send

joined : proj₂ (read-then-send ⊔ writes memory Low) ! memory ≡ just Low
joined = refl

top-greatest : read-then-send ≾ ⊤
top-greatest = holds read-then-send ⊤
