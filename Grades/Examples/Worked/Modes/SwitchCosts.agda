------------------------------------------------------------------------
-- Worked instances of the mode-switch costs.                         --
--                                                                    --
-- A radio is `Off` (mode 0) or `On` (mode 1). Switching it on costs  --
-- 1 and is possible only when it is off, switching it off costs 1    --
-- and is possible only when it is on, and transmitting is free and   --
-- possible only when it is on; from any other mode each gets stuck.  --
-- A round trip, on, transmit, off, takes `Off` back to `Off` at cost --
-- 2 and gets stuck from every other mode. Switching on twice gets    --
-- stuck, and switching off and then on differs from on and then off, --
-- so `_·_` does not commute. A budget of one round trip admits the   --
-- round trip and refuses two. The unit, keeping every mode at no     --
-- cost, is not least. Every ordering is established by the decision  --
-- procedure of the grade, and every computation by reduction.        --
------------------------------------------------------------------------

module Grades.Examples.Worked.Modes.SwitchCosts where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Examples.Modes.SwitchCosts

open import Util.Equality

private
  module G = Grade (mode-switch-costs {ℕᴰ})

open G using (Carrier; _≾_; _≾?_; _≃_; _≃?_; _·_; _⊔_; 𝟏)

holds : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
holds c d {p} = toWitness p

fails : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
fails c d {p} = toWitnessFalse p

same : (c d : Carrier) {p : True (c ≃? d)} → c ≃ d
same c d {p} = toWitness p

Off On : Point
Off = ⟨ 0 ⟩
On  = ⟨ 1 ⟩

switch-on switch-off transmit : Carrier
switch-on  = decided (listing ((Off , On , cost 1) ∷ []))
switch-off = decided (listing ((On , Off , cost 1) ∷ []))
transmit   = decided (listing ((On , On , cost 0) ∷ []))

-- a round trip

round-trip : Carrier
round-trip = decided (listing ((Off , Off , cost 2) ∷ []))

on-transmit-off : switch-on · transmit · switch-off ≃ round-trip
on-transmit-off = same (switch-on · transmit · switch-off) round-trip

-- its costs, computed

off-to-off : entryᵐ round-trip ⌜ 0 ⌝ ⌜ 0 ⌝ ≡ cost 2
off-to-off = refl

on-gets-stuck : entryᵐ round-trip ⌜ 1 ⌝ stuck ≡ cost 0
on-gets-stuck = refl

others-get-stuck : entryᵐ round-trip ⌜ 7 ⌝ stuck ≡ cost 0
others-get-stuck = refl

-- switching on twice gets stuck from every mode

twice-stuck : switch-on · switch-on ≃ decided (listing ((Off , ✗ , cost 1) ∷ []))
twice-stuck = same (switch-on · switch-on) (decided (listing ((Off , ✗ , cost 1) ∷ [])))

-- the order of switching matters

not-commutative : ¬ (switch-on · switch-off ≾ switch-off · switch-on)
not-commutative = fails (switch-on · switch-off) (switch-off · switch-on)

-- a budget of one round trip

two-round-trips-refused : ¬ (round-trip · round-trip ≾ round-trip)
two-round-trips-refused = fails (round-trip · round-trip) round-trip

-- a branch transmitting or not: from `On` it keeps the mode at no
-- cost, from every other mode it keeps the mode or gets stuck

branch : transmit ⊔ 𝟏 ≃ decided (listing ((On , On , cost 0) ∷ (⋆ , ⋆ , cost 0) ∷ (⋆ , ✗ , cost 0) ∷ (Off , Off , cost 0) ∷ (Off , ✗ , cost 0) ∷ []))
branch = same (transmit ⊔ 𝟏) (decided (listing ((On , On , cost 0) ∷ (⋆ , ⋆ , cost 0) ∷ (⋆ , ✗ , cost 0) ∷ (Off , Off , cost 0) ∷ (Off , ✗ , cost 0) ∷ [])))

-- the unit is not least, and the only grade below it is itself

unit-not-least : ¬ (𝟏 ≾ transmit)
unit-not-least = fails 𝟏 transmit

transmit-not-below-unit : ¬ (transmit ≾ 𝟏)
transmit-not-below-unit = fails transmit 𝟏
