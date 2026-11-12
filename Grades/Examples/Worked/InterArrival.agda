------------------------------------------------------------------------
-- Worked instances of the inter-arrival grades, in rational time,    --
-- the operations named by natural numbers.                           --
--                                                                    --
-- The unit is not least: a call is not above it, the unit being      --
-- silent for no time. The product does not commute: a call taking    --
-- one unit and then a delay of one unit has a tail of two units, the --
-- delay and then the call a lead time of one unit.                   --
--                                                                    --
-- A loop calling `beat`, which takes 0.1 to 0.5 units, and then      --
-- `work`, which takes 1 to 3, keeps the gaps between beats within    --
-- 3.5 units; the closure of one round, the grade of any positive     --
-- number of them, is a loop invariant saying so. With a second call  --
-- of `work` the gaps reach 6.5.                                      --
--                                                                    --
-- A resource for exactly two `beep`s, the first at once, the second  --
-- 200 to 300 units after it, and the end at most 10 units after the  --
-- second (`fresh-gain`), admits two beeps 250 units apart, and       --
-- refuses one beep, two beeps 100 units apart, and a call of `draw`  --
-- after the second beep.                                             --
--                                                                    --
-- Every ordering is established by the decision procedure of the     --
-- grade, and every computation by reduction.                         --
------------------------------------------------------------------------

module Grades.Examples.Worked.InterArrival where

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing; from-just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade; Plus)
open import Grades.Hints using (GradeHints)
open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ)
open import Grades.Indexed using (ℕ-names)
import Grades.Examples.Time.Interval as C
open import Grades.Examples.Time.Rational.Interval
  using (Interval; [_,_]; ]_,_]; pointⁱ; ⊤ⁱ; ↑_; _/_; #_; nonZero)
open import Grades.Examples.InterArrival ℚ≥0ᵀ ℕ-names

open import Util.Equality

private
  module E = Grade entryᵍ
  module G = Grade inter-arrival

IA : Set
IA = G.Carrier

-- orderings, established by the decision procedures

holdsᵉ : (c d : Entry) {p : True (c E.≾? d)} → c E.≾ d
holdsᵉ c d {p} = toWitness p

failsᵉ : (c d : Entry) {p : False (c E.≾? d)} → ¬ (c E.≾ d)
failsᵉ c d {p} = toWitnessFalse p

holds : (c d : IA) {p : True (c G.≾? d)} → c G.≾ d
holds c d {p} = toWitness p

fails : (c d : IA) {p : False (c G.≾? d)} → ¬ (c G.≾ d)
fails c d {p} = toWitnessFalse p

------------------------------------------------------------------------
-- One operation

-- a call taking one unit, and a delay of one unit

call delay : Entry
call  = entry nothing (just (act C.[ 1 , C.↑ 1 ] (pointⁱ (# 0)) nothing (pointⁱ (# 1))))
delay = E.ι (# 1)

-- the unit is not least

unit-not-least : ¬ (E.𝟏 E.≾ call)
unit-not-least = failsᵉ E.𝟏 call

-- the product does not commute: the call and then the delay ends two
-- units after the call, the delay and then the call starts it one unit
-- in

call-delay : call E.· delay
           ≡ entry nothing (just (act C.[ 1 , C.↑ 1 ] (pointⁱ (# 0)) nothing (pointⁱ (# 2))))
call-delay = refl

delay-call : delay E.· call
           ≡ entry nothing (just (act C.[ 1 , C.↑ 1 ] (pointⁱ (# 1)) nothing (pointⁱ (# 1))))
delay-call = refl

not-commutative : ¬ (call E.· delay E.≾ delay E.· call)
not-commutative = failsᵉ (call E.· delay) (delay E.· call)

not-commutative′ : ¬ (delay E.· call E.≾ call E.· delay)
not-commutative′ = failsᵉ (delay E.· call) (call E.· delay)

------------------------------------------------------------------------
-- All operations

beat work beep draw : ℕ
beat = 0
work = 1
beep = 2
draw = 3

-- the entry `e` at the operation `x`, the others and the total duration
-- unconstrained

only : ℕ → Entry → IA
only x e = (⊤ᵉ ∣ ((x , e) ∷ [])) , ⊤ⁱ

-- the unit is not least, and the product does not commute

unit-not-least-all : ¬ (G.𝟏 G.≾ occurrence beat (pointⁱ (# 1)))
unit-not-least-all = fails G.𝟏 (occurrence beat (pointⁱ (# 1)))

not-commutative-all : ¬ (occurrence beat (pointⁱ (# 1)) G.· delays (pointⁱ (# 1))
                         G.≾ delays (pointⁱ (# 1)) G.· occurrence beat (pointⁱ (# 1)))
not-commutative-all =
  fails (occurrence beat (pointⁱ (# 1)) G.· delays (pointⁱ (# 1)))
        (delays (pointⁱ (# 1)) G.· occurrence beat (pointⁱ (# 1)))

------------------------------------------------------------------------
-- A loop calling `beat` and then `work`

beat-time work-time : Interval
beat-time = [ 1 / 10 , ↑ 1 / 2 ]
work-time = [ # 1 , ↑ # 3 ]

round round₂ : IA
round  = occurrence beat beat-time G.· occurrence work work-time
round₂ = round G.· occurrence work work-time

-- gaps between beats of at most 3.5 units

beats-apart : IA
beats-apart = only beat (entry nothing (just (act C.[ 1 , C.∞ ] ⊤ⁱ (just [ # 0 , ↑ 7 / 2 ]) ⊤ⁱ)))

-- two rounds: two beats, the first at once, 1.1 to 3.5 units apart, and
-- the end 1.1 to 3.5 units after the second

two-rounds-at-beat : proj₁ (round G.· round) ! beat
                   ≡ entry nothing (just (act C.[ 2 , C.↑ 2 ] (pointⁱ (# 0))
                                              (just [ 11 / 10 , ↑ 7 / 2 ]) [ 11 / 10 , ↑ 7 / 2 ]))
two-rounds-at-beat = refl

two-rounds : round G.· round G.≾ beats-apart
two-rounds = holds (round G.· round) beats-apart

-- the closure of a round, the grade of any positive number of rounds,
-- a loop invariant: the beats stay 1.1 to 3.5 units apart

rounds : IA
rounds = Plus.c⁺ (from-just (GradeHints.plus? inter-arrivalʰ round))

rounds-at-beat : proj₁ rounds ! beat
               ≡ entry nothing (just (act C.[ 1 , C.∞ ] (pointⁱ (# 0))
                                          (just [ 11 / 10 , ↑ 7 / 2 ]) [ 11 / 10 , ↑ 7 / 2 ]))
rounds-at-beat = refl

rounds-apart : rounds G.≾ beats-apart
rounds-apart = holds rounds beats-apart

-- with a second call of `work` the gaps reach 6.5

two-longer-rounds-refused : ¬ (round₂ G.· round₂ G.≾ beats-apart)
two-longer-rounds-refused = fails (round₂ G.· round₂) beats-apart

two-longer-rounds : round₂ G.· round₂
                  G.≾ only beat (entry nothing (just (act C.[ 1 , C.∞ ] ⊤ⁱ (just [ # 0 , ↑ 13 / 2 ]) ⊤ⁱ)))
two-longer-rounds =
  holds (round₂ G.· round₂)
        (only beat (entry nothing (just (act C.[ 1 , C.∞ ] ⊤ⁱ (just [ # 0 , ↑ 13 / 2 ]) ⊤ⁱ))))

------------------------------------------------------------------------
-- Exactly two beeps, the first at once, the second 200 to 300 units
-- after it, and the end at most 10 units after the second

fresh-gain : IA
fresh-gain = only beep (entry nothing (just
  (act C.[ 2 , C.↑ 2 ] [ # 0 , ↑ # 0 ] (just [ # 200 , ↑ # 300 ]) [ # 0 , ↑ # 10 ])))

-- a beep takes more than 0 and at most 1 unit, a drawing 20 to 30

beep-time draw-time : Interval
beep-time = ] # 0 , ↑ # 1 ]
draw-time = [ # 20 , ↑ # 30 ]

beeps : Interval → IA
beeps d = occurrence beep beep-time G.· delays d G.· occurrence beep beep-time

two-beeps : beeps (pointⁱ (# 250)) G.≾ fresh-gain
two-beeps = holds (beeps (pointⁱ (# 250))) fresh-gain

one-beep-refused : ¬ (occurrence beep beep-time G.≾ fresh-gain)
one-beep-refused = fails (occurrence beep beep-time) fresh-gain

early-beep-refused : ¬ (beeps (pointⁱ (# 100)) G.≾ fresh-gain)
early-beep-refused = fails (beeps (pointⁱ (# 100))) fresh-gain

drawing-refused : ¬ (beeps (pointⁱ (# 250)) G.· occurrence draw draw-time G.≾ fresh-gain)
drawing-refused = fails (beeps (pointⁱ (# 250)) G.· occurrence draw draw-time) fresh-gain
