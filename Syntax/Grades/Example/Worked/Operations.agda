------------------------------------------------------------------------
-- The alphabet the worked examples are built over.                    --
--                                                                     --
-- A small sensor node: it can `read` a sensor, `write` a reading back  --
-- to local memory, and `send` one over the radio. The three differ in  --
-- what they cost, which is what makes the orderings interesting:       --
--                                                                     --
--   read   1 tick     cheap, local                                     --
--   write  2-3 ticks  local, but a memory write may stall              --
--   send   4-6 ticks  expensive, and variable                          --
--                                                                     --
-- Two cost models are read off those figures -- `fast`, the best case, --
-- and `slow`, the worst case -- and `opTime` packages them as the      --
-- interval an operation's execution time falls in. `cost` is `slow`:   --
-- the conservative model, which is what a schedule must budget for.    --
--                                                                     --
-- Everything about timed traces over this alphabet is re-exported, so  --
-- the sibling modules need only import this one.                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Operations where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; _≤_; s≤s; z≤n)
open import Data.Unit using (tt)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)

open import Syntax.Grades.Example.Interval.TwoSided using (Interval; [_,_,_])

open import Util.Equality

------------------------------------------------------------------------
-- The operation symbols

data Op : Set where
  read  : Op
  write : Op
  send  : Op

_≟ₒ_ : DecidableEquality Op
read  ≟ₒ read  = yes refl
read  ≟ₒ write = no λ ()
read  ≟ₒ send  = no λ ()
write ≟ₒ read  = no λ ()
write ≟ₒ write = yes refl
write ≟ₒ send  = no λ ()
send  ≟ₒ read  = no λ ()
send  ≟ₒ write = no λ ()
send  ≟ₒ send  = yes refl

------------------------------------------------------------------------
-- Execution times

-- the interval an operation's execution time falls in

opTime : Op → Interval
opTime read  = [ 1 , 1 , s≤s z≤n ]
opTime write = [ 2 , 3 , s≤s (s≤s z≤n) ]
opTime send  = [ 4 , 6 , s≤s (s≤s (s≤s (s≤s z≤n))) ]

-- the two endpoints, as cost models in their own right

fast slow : Op → ℕ
fast read  = 1
fast write = 2
fast send  = 4

slow read  = 1
slow write = 3
slow send  = 6

fast≤slow : (o : Op) → fast o ≤ slow o
fast≤slow read  = s≤s z≤n
fast≤slow write = s≤s (s≤s z≤n)
fast≤slow send  = s≤s (s≤s (s≤s (s≤s z≤n)))

-- the cost model the worked examples use: the conservative one, which
-- is what a schedule has to budget for

cost : Op → ℕ
cost = slow

------------------------------------------------------------------------
-- Timed traces over this alphabet

open import Syntax.Grades.Traces.Sets Op public
open import Syntax.Grades.Traces.Durations Op public

-- `duration` measures a trace against `cost` unless said otherwise

open Durations cost public using (duration)

------------------------------------------------------------------------
-- Writing down finite sets of traces
--
-- A grade is a non-empty finite set; at these sizes, spelling out the
-- list is clearer than any notation for it.

set₁ : Trace → NeTraces
set₁ t = neTraces (t ∷ []) tt

set₂ : Trace → Trace → NeTraces
set₂ t u = neTraces (t ∷ u ∷ []) tt

set₃ : Trace → Trace → Trace → NeTraces
set₃ t u v = neTraces (t ∷ u ∷ v ∷ []) tt

------------------------------------------------------------------------
-- Some named runs of the node

-- read the sensor and stop

poll : Trace
poll = ⌈ read ⌉

-- read the sensor, then store the reading

logged : Trace
logged = ⌈ read ⌉ ∙ ⌈ write ⌉

-- read the sensor, idle for two ticks, then transmit

uplink : Trace
uplink = ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉

-- their durations under `cost`, by computation

poll-takes-1 : duration poll ≡ 1
poll-takes-1 = refl

logged-takes-4 : duration logged ≡ 4
logged-takes-4 = refl

uplink-takes-9 : duration uplink ≡ 9
uplink-takes-9 = refl
