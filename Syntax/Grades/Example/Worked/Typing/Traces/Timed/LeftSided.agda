------------------------------------------------------------------------
-- Typed example computations at the grade of trace guarantees.        --
--                                                                     --
-- Effect grades and resource grades are both sets of timed traces at   --
-- the coverage order, and each operation is graded by the one-event    --
-- run that performs it. A grade lists guarantees, and a computation    --
-- sits below it when each of its runs *covers* one of them: every      --
-- operation the guarantee names has occurred, and every delay it names --
-- has been paid out of the run's own time, operations counted at       --
-- `cost` -- read 1, write 3, send 6.                                   --
--                                                                     --
-- So this is the trace counterpart of the lower-bound intervals: the   --
-- grade says what has definitely happened, and `coerce` may forget     --
-- part of it. `unbox`'s premise then reads "the work the box asks for  --
-- has been done", which -- unlike a time bound -- can ask for          --
-- particular operations. Idling discharges a demand for time and never --
-- a demand for a reading, and that is the refusal this grade adds.     --
--                                                                     --
-- As at the lower bounds, nothing goes stale (every run covers the     --
-- empty guarantee) and no handler clause may drop its continuation     --
-- (returning at once covers nothing).                                  --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Timed.LeftSided where

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_; cost;
         NeTraces; traces; ε; _∙_; ⌈_⌉; ⟨_⟩; ⟅_⟆; ⟅_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
  using (left-sided; holds; fails; failsᵉ)

open import Syntax.Grades.Traces.Coverage.AsOrder Op _≟ₒ_ cost
  using (coverageOrder)

open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ coverageOrder
  using (u-≽ˢ)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them

opTime : Op → NeTraces
opTime o = ⟅ ⌈ o ⌉ ⟆

open import Syntax.Grades.Example.Worked.Typing.Core left-sided opTime

------------------------------------------------------------------------
-- Effectful computations

sampling : [] ⊢C⦂ Reading ‼ ⟅ ⌈ read ⌉ ⟆
sampling = perform read ⋆ (return here)

storing : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing = perform read ⋆ (perform write here (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
relaying = perform read ⋆ (perform send here (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
tagged-relaying =
  perform read ⋆
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
      `in perform send here (return ⋆))

-- a computation that only idles, which guarantees time and no work

idling : [] ⊢C⦂ Unit ‼ ⟅ ⟨ 5 ⟩ ⟆
idling = delay 5 (return ⋆)

------------------------------------------------------------------------
-- Nothing goes stale
--
-- `var`'s bound is `ρ ≾ᵣ uᵣ`, and every run covers the empty
-- guarantee, so a reading survives whatever happens after it.

nothing-goes-stale : (ρ : R) → ρ ≾ᵣ uᵣ
nothing-goes-stale ρ = u-≽ˢ (traces ρ)

-- take a reading, idle two ticks, and transmit the reading taken
-- before the idling

idle-then-transmit : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
idle-then-transmit =
  perform read ⋆
    (delay 2
      (perform send (fresh-var (nothing-goes-stale _) (Tl-⟨⟩ Hd))
        (return ⋆)))

carried-reading : [] ∷ Reading ⊢C⦂ Reading ‼ ⟅ ⌈ read ⌉ ⟆
carried-reading =
  perform read ⋆
    (return (fresh-var (nothing-goes-stale _) (Tl-∷ (Tl-⟨⟩ Hd))))

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆ (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves up the order, and up means "guarantees less": a run
-- may forget the operations it performed, or trade them for the time
-- they took.

forgetting-the-store : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ⟆
forgetting-the-store =
  coerce holds (perform read ⋆ (perform write here (return ⋆)))

keeping-only-the-time : [] ⊢C⦂ Reading ‼ ⟅ ⟨ 1 ⟩ ⟆
keeping-only-the-time = coerce holds (perform read ⋆ (return here))

-- and never more time than the run takes

no-more-time : ¬ (opTime read ·ₑ uₑ ≾ₑ ⟅ ⟨ 2 ⟩ ⟆)
no-more-time = fails

-- nor an operation the run never performed: time buys no work here,
-- which is the direction this order refuses

idling-guarantees-no-reading : ¬ (of-natᵉ 5 ·ₑ uₑ ≾ₑ ⟅ ⌈ read ⌉ ⟆)
idling-guarantees-no-reading = fails

------------------------------------------------------------------------
-- Conditional branching
--
-- The conditional's grade has to be guaranteed by both branches. The
-- union does it, each branch guaranteeing its own run; so does the time
-- the two branches are both bound to spend.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

timed-branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ⟅ ⟨ 3 ⟩ ⟆
timed-branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

-- four ticks are more than the storing branch guarantees

four-ticks-not-guaranteed : ¬ (opTime write ·ₑ uₑ ≾ₑ ⟅ ⟨ 4 ⟩ ⟆)
four-ticks-not-guaranteed = fails

-- an `if` over data alone needs no common grade to be found: both
-- branches make the same run

either-reading : [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ⟆
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

sampling-then-branching :
  [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
sampling-then-branching =
  perform read ⋆
    (if true
      `then coerce holds (perform send  here (return ⋆))
      `else coerce holds (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a resource that comes due when work has been done
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`: what the computation did between
-- boxing the resource and claiming it has to cover what the box asks
-- for. The box below asks for a reading.

demand : R
demand = ⟅ ⌈ read ⌉ ⟆

claim-after-sampling : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-sampling =
  box {ρ = demand} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
        (perform send here (return ⋆))))

handed-over : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box {ρ = demand} (const 42)
    (lam (perform read ⋆
           (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
             (perform send here (return ⋆))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box {ρ = demand} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- idling does not discharge a demand for a reading, however long it
-- goes on

idling-does-not-discharge-it : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ demand)
idling-does-not-discharge-it = fails

-- and neither does doing nothing at all

claiming-at-once : ¬ (uᵣ ≾ᵣ demand)
claiming-at-once = failsᵉ uᵣ demand

-- a demand for *time* is discharged by anything that takes it, work
-- included: two ticks of idling, or a store, both cover two ticks

waiting : R
waiting = ⟅ ⟨ 2 ⟩ ⟆

claim-after-idling : [] ⊢C⦂ Unit ‼ ⟅ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
claim-after-idling =
  box {ρ = waiting} (const 42)
    (delay 2
      (unbox (Tl-⟨⟩ Hd) holds
        (perform send here (return ⋆))))

storing-covers-it : uᵣ ·ᵣ opTime write ≾ᵣ waiting
storing-covers-it = holds

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- A box asking for either of two runs is within both branches' reach,
-- and the conditional is graded by what both branches guarantee -- here
-- a transmission, which each branch makes.

alternatives : R
alternatives = ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆

claimed-in-both-branches : [] ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ⟆
claimed-in-both-branches =
  box {ρ = alternatives} (const 42)
    (if true
      `then coerce holds
              (perform read ⋆
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                  (perform send here (return ⋆))))
      `else coerce holds
              (perform send (const 0)
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                  (perform send here (return ⋆)))))

-- asking for the reading alone puts it out of the transmitting
-- branch's reach

sampling-branch-covers-it : uᵣ ·ᵣ opTime read ≾ᵣ demand
sampling-branch-covers-it = holds

transmitting-branch-does-not : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ demand)
transmitting-branch-does-not = fails

------------------------------------------------------------------------
-- Programs written at these guarantees
--
-- A box asking for three ticks' worth of work, claimed on both sides of
-- an `if`: one branch stores a reading, which takes three ticks, and
-- the other idles for three. Both then transmit, so both guarantee
-- nine ticks, and that is the conditional's grade.

three-ticks : R
three-ticks = ⟅ ⟨ 3 ⟩ ⟆

work-or-wait : [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⟨ 9 ⟩ ⟆
work-or-wait =
  box {ρ = three-ticks} (const 42)
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce holds
              (perform write (const 0)
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                  (perform send here (return ⋆))))
      `else coerce holds
              (delay 3
                (unbox (Tl-⟨⟩ Hd) holds
                  (perform send here (return ⋆)))))

-- ten ticks are more than either branch guarantees

ten-ticks-not-guaranteed :
  ¬ (opTime write ·ₑ (opTime send ·ₑ uₑ) ≾ₑ ⟅ ⟨ 10 ⟩ ⟆)
ten-ticks-not-guaranteed = fails

-- and a branch that only takes a reading would not cover the box: one
-- tick against the three it asks for

sampling-branch-too-little : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ three-ticks)
sampling-branch-too-little = fails

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ ⟅ ⌈ read ⌉ ⟆
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in (return here)

identified : Node ⊢C⦂ NodeId ‼ ⟅ ⌈ read ⌉ ⟆
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: it is graded by a guarantee that
-- names the operation, and returning at once covers nothing

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = failsᵉ uₑ (op-grade read ·ₑ uₑ)
