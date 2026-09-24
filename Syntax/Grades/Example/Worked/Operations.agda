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
-- interval an operation's execution time falls in. A guarantee is      --
-- credited at `costˡᵒ = fast`, since that is all an operation is       --
-- certain to take; an allowance is charged `costʰⁱ = slow`, which is   --
-- what a schedule must budget for.                                     --
--                                                                     --
-- Everything about timed traces over this alphabet is re-exported, so  --
-- the sibling modules need only import this one.                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Operations where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; _≤_; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Nullary using (yes; no)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_]; ↑_)

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

-- The symbols are ordered as declared, which is also by increasing
-- cost: `read` below `write` below `send`.

infix 4 _<ᵒ_

data _<ᵒ_ : Rel Op lzero where
  read<write : read  <ᵒ write
  read<send  : read  <ᵒ send
  write<send : write <ᵒ send

<ᵒ-trans : Transitive _<ᵒ_
<ᵒ-trans read<write write<send = read<send
<ᵒ-trans read<send  ()
<ᵒ-trans write<send ()

<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_
<ᵒ-cmp read  read  = tri≈ (λ ()) refl (λ ())
<ᵒ-cmp read  write = tri< read<write (λ ()) (λ ())
<ᵒ-cmp read  send  = tri< read<send (λ ()) (λ ())
<ᵒ-cmp write read  = tri> (λ ()) (λ ()) read<write
<ᵒ-cmp write write = tri≈ (λ ()) refl (λ ())
<ᵒ-cmp write send  = tri< write<send (λ ()) (λ ())
<ᵒ-cmp send  read  = tri> (λ ()) (λ ()) read<send
<ᵒ-cmp send  write = tri> (λ ()) (λ ()) write<send
<ᵒ-cmp send  send  = tri≈ (λ ()) refl (λ ())

------------------------------------------------------------------------
-- Execution times

-- the interval an operation's execution time falls in

opTime : Op → Interval∞
opTime read  = [ 1 , ↑ 1 ]
opTime write = [ 2 , ↑ 3 ]
opTime send  = [ 4 , ↑ 6 ]

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

-- the two cost models the worked examples use, one per side of an
-- interval: a floor credits an operation with its best case, a cap
-- charges it its worst

costˡᵒ costʰⁱ : Op → ℕ
costˡᵒ = fast
costʰⁱ = slow

cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o
cost-≤ = fast≤slow

-- every operation takes time, which is what makes an empty allowance
-- permit nothing but the empty run

costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o
costʰⁱ-pos read  = s≤s z≤n
costʰⁱ-pos write = s≤s z≤n
costʰⁱ-pos send  = s≤s z≤n

------------------------------------------------------------------------
-- Timed traces over this alphabet

open import Syntax.Grades.Traces.Sets Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans public
open import Syntax.Grades.Traces.Durations Op public

-- a trace is measured at either cost model

open Durations costˡᵒ public using () renaming (duration to durationˡᵒ)
open Durations costʰⁱ public using () renaming (duration to durationʰⁱ)

------------------------------------------------------------------------
-- Writing down finite sets of traces
--
-- `⟅ t ∣ u ⟆` is the set whose members are `t` and `u`. At these sizes
-- writing the members out is the clearest thing to do. The members may
-- be given in whatever order reads best, and are normalised into the
-- canonical one: naming a trace twice names the same set as once.

⟅_⟆ : Trace → NeTraces
⟅ t ⟆ = neSet (t ∷ []) tt

⟅_∣_⟆ : Trace → Trace → NeTraces
⟅ t ∣ u ⟆ = neSet (t ∷ u ∷ []) tt

⟅_∣_∣_⟆ : Trace → Trace → Trace → NeTraces
⟅ t ∣ u ∣ v ⟆ = neSet (t ∷ u ∷ v ∷ []) tt

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

-- the uplink with the reading also stored on the way

logged-uplink : Trace
logged-uplink = ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉

-- the uplink, transmitting twice

chatty-uplink : Trace
chatty-uplink = uplink ∙ ⌈ send ⌉

-- idling for two ticks and doing nothing at all

idle : Trace
idle = ⟨ 2 ⟩

-- their best- and worst-case durations, by computation

poll-takes-1-to-1 : durationˡᵒ poll ≡ 1 × durationʰⁱ poll ≡ 1
poll-takes-1-to-1 = refl , refl

logged-takes-3-to-4 : durationˡᵒ logged ≡ 3 × durationʰⁱ logged ≡ 4
logged-takes-3-to-4 = refl , refl

uplink-takes-7-to-9 : durationˡᵒ uplink ≡ 7 × durationʰⁱ uplink ≡ 9
uplink-takes-7-to-9 = refl , refl

logged-uplink-takes-9-to-12 :
  durationˡᵒ logged-uplink ≡ 9 × durationʰⁱ logged-uplink ≡ 12
logged-uplink-takes-9-to-12 = refl , refl

chatty-uplink-takes-11-to-15 :
  durationˡᵒ chatty-uplink ≡ 11 × durationʰⁱ chatty-uplink ≡ 15
chatty-uplink-takes-11-to-15 = refl , refl
