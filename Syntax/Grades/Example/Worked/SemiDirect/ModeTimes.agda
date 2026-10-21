------------------------------------------------------------------------
-- Worked instances of the mode times.                                --
--                                                                    --
-- A reagent is in a cold block (`Cold`, mode 0) or out of it (`Out`, --
-- mode 1). Taking it out takes one or two steps in the block and is  --
-- possible only from `Cold`; putting it back takes one step out of   --
-- the block and is possible only from `Out`; from any other mode     --
-- each gets stuck at no time. Taking it out, waiting twenty steps    --
-- and putting it back spends one or two steps in the block and       --
-- twenty-one out of it, twenty-two or twenty-three in all. A         --
-- protocol allowing at most thirty steps out of the block admits     --
-- this and refuses a wait of thirty steps. Putting back first gets   --
-- stuck from `Cold`, so `_·_` does not commute; the unit, keeping    --
-- every mode at no time, is not least. Every ordering is established --
-- by the decision procedure of the grade, and every computation by   --
-- reduction.                                                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.SemiDirect.ModeTimes where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Syntax.Durations.Nat using (ℕᴰ)
open import Syntax.Grades using (Grade)
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using (Interval∞; [_,_]; ↑_; ∞)
open import Syntax.Grades.Indexed using (ℕ-names; module Maps)
open import Syntax.Grades.Example.SemiDirect.ModeTimes.Boxes using (witness)
open import Syntax.Grades.Example.SemiDirect.ModeTimes
open import Syntax.Grades.Matrix.Modes ℕ-names using (⌜_⌝)

open import Util.Equality

open Maps ℕ-names using (_∣_)

private
  module G = Grade mode-times

open G using (Carrier; _≾_; _≾?_; _≃_; _≃?_; _·_; _⊔_; u; of-dur)

holds : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
holds c d {p} = toWitness p

fails : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
fails c d {p} = toWitnessFalse p

same : (c d : Carrier) {p : True (c ≃? d)} → c ≃ d
same c d {p} = toWitness p

Cold Out : Point
Cold = ⟨ 0 ⟩
Out  = ⟨ 1 ⟩

take put-back : Carrier
take     = occurrence ((Cold , Out) ∷ []) [ 1 , ↑ 2 ]
put-back = occurrence ((Out , Cold) ∷ []) [ 1 , ↑ 1 ]

-- out for twenty steps

excursion : Carrier
excursion = take · of-dur 20 · put-back

-- its entry from `Cold` to `Cold`: one or two steps in the block,
-- twenty-one out, twenty-two or twenty-three in all

expected : Carrier
expected = listed (0 ∷ 1 ∷ [])
  ((Cold , Cold , bounds ([ 0 , ↑ 0 ] ∣ ((0 , [ 1 , ↑ 2 ]) ∷ (1 , [ 21 , ↑ 21 ]) ∷ []))
                         [ 22 , ↑ 23 ]
                         (witness ((0 , 1) ∷ (1 , 21) ∷ []) ((λ { (Data.List.Relation.Unary.Any.here ()) ; (Data.List.Relation.Unary.Any.there ()) }) , (λ ()) , tt))) ∷ [])
  where import Data.List.Relation.Unary.Any

excursion-times : excursion ≃ expected
excursion-times = same excursion expected

-- a protocol: at most thirty steps out of the block, from `Cold` back
-- to `Cold`, the other modes and the total unconstrained

protocol : Carrier
protocol = listed (0 ∷ 1 ∷ [])
  ((Cold , Cold , bounds ([ 0 , ∞ ] ∣ ((1 , [ 0 , ↑ 30 ]) ∷ [])) [ 0 , ∞ ] (witness [] tt)) ∷ [])

excursion-allowed : excursion ≾ protocol
excursion-allowed = holds excursion protocol

-- thirty steps out, and the putting back, are too long

too-long : ¬ (take · of-dur 30 · put-back ≾ protocol)
too-long = fails (take · of-dur 30 · put-back) protocol

-- a delay spends its time in the mode it keeps

delay-out : entryᵐ (of-dur 5) ⌜ 1 ⌝ ⌜ 1 ⌝ ≡ spent [ 5 , ↑ 5 ] 1
delay-out = refl

-- putting back first gets stuck from `Cold`, so the order matters

not-commutative : ¬ (put-back · take ≾ take · put-back)
not-commutative = fails (put-back · take) (take · put-back)

-- a branch waiting five or ten steps out of the block: the hull

branch : take · (of-dur 5 ⊔ of-dur 10) · put-back ≾ protocol
branch = holds (take · (of-dur 5 ⊔ of-dur 10) · put-back) protocol

-- the unit is not least, and an operation is not below it

unit-not-least : ¬ (u ≾ take)
unit-not-least = fails u take

take-not-below-unit : ¬ (take ≾ u)
take-not-below-unit = fails take u
