------------------------------------------------------------------------
-- What the time-strict sub-trace order changes, on the node's own      --
-- alphabet.                                                            --
--                                                                     --
-- Both orders are decided, so each claim below is closed by running    --
-- the relevant decision procedure: the separation is checked, not      --
-- asserted.                                                            --
--                                                                     --
-- The demand throughout is                                             --
--                                                                     --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉                                       --
--                                                                     --
-- "read, then let two ticks pass, then send". Under `cost` a write     --
-- takes three ticks, so a write is always enough time to pay the two   --
-- the demand asks for. The question the two orders answer differently  --
-- is *where* that write has to happen.                                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.SubtraceTimed.Order where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.Subtrace Op cost
  using (_≼_; module DecSubtrace)
open import Syntax.Grades.Traces.SubtraceTimed.Core Op cost
  using (_≼ᵗ_)
open import Syntax.Grades.Traces.SubtraceTimed.Decidable Op cost
  using (module DecSubtraceTimed)

open DecSubtrace _≟ₒ_ using (_≼?_)
open DecSubtraceTimed _≟ₒ_ using (_≼ᵗ?_)

holdsˡᵉⁿ : {s t : Trace} {p : True (s ≼? t)} → s ≼ t
holdsˡᵉⁿ {p = p} = toWitness p

failsˡᵉⁿ : {s t : Trace} {p : False (s ≼? t)} → ¬ (s ≼ t)
failsˡᵉⁿ {p = p} = toWitnessFalse p

holdsᵗ : {s t : Trace} {p : True (s ≼ᵗ? t)} → s ≼ᵗ t
holdsᵗ {p = p} = toWitness p

failsᵗ : {s t : Trace} {p : False (s ≼ᵗ? t)} → ¬ (s ≼ᵗ t)
failsᵗ {p = p} = toWitnessFalse p

------------------------------------------------------------------------
-- The write happens between the read and the send
--
-- Both orders accept this: the three ticks the write takes fall inside
-- the window the demand places them in.

between-lenient : (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                ≼ (⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉)
between-lenient = holdsˡᵉⁿ

between-timed : (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
              ≼ᵗ (⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉)
between-timed = holdsᵗ

------------------------------------------------------------------------
-- The write happens before the read
--
-- This is the separation. The lenient order accepts it -- the write's
-- three ticks are banked and then spent on a delay the demand places
-- *after* the read -- and the time-strict order does not, because the
-- match on `read` discards whatever was banked before it.

before-lenient : (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
               ≼ (⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉)
before-lenient = holdsˡᵉⁿ

before-timed : ¬ ((⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                ≼ᵗ (⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉))
before-timed = failsᵗ

------------------------------------------------------------------------
-- The write happens after the send
--
-- Here the two orders agree, and it is worth seeing why: banking runs
-- forwards only. To reach the write, the run's `send` must first be
-- banked by `pay-op`, and then nothing is left to match the `send` the
-- demand still asks for. So even the lenient order refuses this -- its
-- permissiveness is about time earned *earlier*, never later.

after-lenient : ¬ ((⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                 ≼ (⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉))
after-lenient = failsˡᵉⁿ

after-timed : ¬ ((⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
               ≼ᵗ (⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉))
after-timed = failsᵗ

------------------------------------------------------------------------
-- Where the two agree
--
-- Time demanded in the same window as it elapses is accepted by both,
-- and an operation is still never bought with time under either.

genuine-idling : (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
               ≼ᵗ (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
genuine-idling = holdsᵗ

-- more idling than demanded, in the right place, is still fine

more-idling : (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
            ≼ᵗ (⌈ read ⌉ ∙ ⟨ 5 ⟩ ∙ ⌈ send ⌉)
more-idling = holdsᵗ

-- but idling never buys the send

idling-is-no-send : ¬ ((⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉) ≼ᵗ (⌈ read ⌉ ∙ ⟨ 100 ⟩))
idling-is-no-send = failsᵗ
