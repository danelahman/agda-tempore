------------------------------------------------------------------------
-- Typed example computations at the grade of trace guarantees.       --
--                                                                    --
-- Effect grades and resource grades are both sets of timed traces at --
-- the coverage order, and each operation is graded by the one-event  --
-- run that performs it. A grade lists guarantees, and a computation  --
-- lies below it when each of its runs covers one of them: every      --
-- operation the guarantee lists has occurred, and every delay it     --
-- lists has elapsed in the run, operations counted at `costˡᵒ` (read --
-- 1, write 2, send 4), the time each is certain to take.             --
--                                                                    --
-- This is the trace counterpart of the lower-bound intervals: the    --
-- grade states what has happened, and `coerce` may forget part of    --
-- it. The premise of `unbox` then states that the operations the box --
-- demands have been performed, which, unlike a time bound, can       --
-- demand particular operations. Idling discharges a demand for time  --
-- and never a demand for a reading; this is the refusal specific to  --
-- this grade.                                                        --
--                                                                    --
-- As at the lower bounds, nothing goes stale (every run covers the   --
-- empty guarantee), and no handler clause may discard its            --
-- continuation (returning at once covers nothing).                   --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. A lock records which operation ran, and the       --
-- premise compares the product of the locks between the binding of a --
-- box and its `unbox` with the box.                                  --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Traces.Timed.LeftSided where

open import Relation.Nullary using (¬_)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costˡᵒ;
         ε; _∙_; ⌈_⌉; ⟨_⟩)

open import Grades.Examples.Worked.Traces.Timed.LeftSided
  using (left-sided; holds; fails; failsᵉ; ≾-⊤; Antichain;
         ⟅_⟆; ⟅_∣_⟆; ⟅_∣_∣_⟆)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them

open import Grades.Examples.Worked.Operations.Grading using (module Traces-Timed-LeftSided)
open Traces-Timed-LeftSided using (opTime) public

open import MonomorphicCalculus.Examples.Typing.Core left-sided opTime

------------------------------------------------------------------------
-- Effectful computations

sampling : [] ⊢C⦂ Reading ! ⟅ ⌈ read ⌉ ⟆
sampling =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform write here              -- ⟨ ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ unit
      (return ⋆))

relaying : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
relaying =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform send here               -- ⟨ ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
tagged-relaying =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

-- a computation that only idles, which guarantees time and no work

idling : [] ⊢C⦂ unit ! ⟅ ⟨ 5 ⟩ ⟆
idling =
  delay 5                            -- ⟨ ⟅ ⟨ 5 ⟩ ⟆ ⟩
    (return ⋆)

------------------------------------------------------------------------
-- Nothing goes stale
--
-- `var`'s bound is `ρ ≾ᵣ 𝟏ᵣ`, and every run covers the empty
-- guarantee, so a reading survives whatever locks stand over it.

nothing-goes-stale : (ρ : R) → ρ ≾ᵣ 𝟏ᵣ
nothing-goes-stale ρ = ≾-⊤ ρ

-- take a reading, idle two ticks, and transmit the reading taken
-- before the idling

idle-then-transmit : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
idle-then-transmit =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (delay 2                         -- ⟨ ⟅ ⟨ 2 ⟩ ⟆ ⟩
      (perform send (fresh-var (nothing-goes-stale _) (Tl-⟨⟩ Hd))
                                     -- ⟨ ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ unit
        (return ⋆)))

carried-reading : [] ∷ Reading ⊢C⦂ Reading ! ⟅ ⌈ read ⌉ ⟆
carried-reading =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (fresh-var (nothing-goes-stale _) (Tl-∷ (Tl-⟨⟩ Hd))))

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ! ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves up the order, and up means "guarantees less": a run
-- may forget the operations it performed, or trade them for the time
-- they took. The context is untouched.

forgetting-the-store : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ⟆
forgetting-the-store =
  coerce holds (perform read ⋆ (perform write here (return ⋆)))

keeping-only-the-time : [] ⊢C⦂ Reading ! ⟅ ⟨ 1 ⟩ ⟆
keeping-only-the-time = coerce holds (perform read ⋆ (return here))

-- and never more time than the run takes

no-more-time : ¬ (opTime read ·ₑ 𝟏ₑ ≾ₑ ⟅ ⟨ 2 ⟩ ⟆)
no-more-time = fails

-- nor an operation the run never performed: time pays for no
-- operation under this order

idling-guarantees-no-reading : ¬ (ιₑ 5 ·ₑ 𝟏ₑ ≾ₑ ⟅ ⌈ read ⌉ ⟆)
idling-guarantees-no-reading = fails

------------------------------------------------------------------------
-- Conditional branching
--
-- The conditional's grade has to be guaranteed by both branches. The
-- union does it, each branch guaranteeing its own run; so does the time
-- the two branches are both bound to spend. Neither branch locks the
-- context.

branching : [] ∷ bool ∷ Reading ⊢C⦂ unit ! ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
branching =
  if eternal-var boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

timed-branching : [] ∷ bool ∷ Reading ⊢C⦂ unit ! ⟅ ⟨ 2 ⟩ ⟆
timed-branching =
  if eternal-var boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

-- three ticks are more than the storing branch guarantees, being the
-- store's worst case rather than its best

three-ticks-not-guaranteed : ¬ (opTime write ·ₑ 𝟏ₑ ≾ₑ ⟅ ⟨ 3 ⟩ ⟆)
three-ticks-not-guaranteed = fails

-- an `if` over data alone needs no common grade to be found: both
-- branches make the same run

either-reading : [] ∷ bool ∷ Reading ∷ Reading ⊢C⦂ unit ! ⟅ ⌈ send ⌉ ⟆
either-reading =
  if eternal-var boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

sampling-then-branching :
  [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
sampling-then-branching =
  perform {ε = ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆} read ⋆
                                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (if true
      `then coerce holds (perform send  here (return ⋆))
      `else coerce holds (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a resource that comes due when work has been done
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`: what the computation did between
-- boxing the resource and claiming it (the locks the comments show)
-- has to cover what the box asks for. The box below asks for a reading.

demand : R
demand = ⟅ ⌈ read ⌉ ⟆

-- the run stores the reading as well before claiming, so the premise
-- is not an equality: `⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆` covers the demand for
-- a reading with the store left over

claim-after-storing : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-storing =
  box demand (const 42)              -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (perform read ⋆                  -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (perform write here            -- ⟨ ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

handed-over : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box demand (const 42)              -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (lam                             -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
       (perform read ⋆               -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

-- and the claim survives extra work in between: two readings cover a
-- demand for one, so the function may sample again before claiming
-- what it was handed. Two locks stand between the binding and the
-- claim, and their product is `⟅ ⌈ read ⌉ ∙ ⌈ read ⌉ ⟆`.

handed-over' : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over' =
  box demand (const 42)              -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (lam                             -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
       (perform read ⋆               -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (perform read ⋆             -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
           (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
             (perform send here (return ⋆)))))
      · here)

either-way : [] ∷ bool ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box demand (const 42)              -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (perform read ⋆                  -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
        (if eternal-var boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- idling does not discharge a demand for a reading, however long it
-- goes on

idling-does-not-discharge-it : ¬ (𝟏ᵣ ·ᵣ ιᵣ 2 ≾ᵣ demand)
idling-does-not-discharge-it = fails

-- and neither does doing nothing at all: with no lock in between there
-- is nothing to cover the demand with

claiming-at-once : ¬ (𝟏ᵣ ≾ᵣ demand)
claiming-at-once = failsᵉ 𝟏ᵣ demand

-- a demand for time is discharged by anything that takes it, work
-- included: two ticks of idling, or a store, both cover two ticks

waiting : R
waiting = ⟅ ⟨ 2 ⟩ ⟆

claim-after-idling : [] ⊢C⦂ unit ! ⟅ ⟨ 3 ⟩ ∙ ⌈ send ⌉ ⟆
claim-after-idling =
  box waiting (const 42)             -- ∷ [ ⟅ ⟨ 2 ⟩ ⟆ ] Reading
    (delay 3                         -- ⟨ ⟅ ⟨ 3 ⟩ ⟆ ⟩
      (unbox (Tl-⟨⟩ Hd) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

storing-covers-it : 𝟏ᵣ ·ᵣ opTime write ≾ᵣ waiting
storing-covers-it = holds

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- A box asking for either of two runs is within both branches' reach,
-- and the conditional is graded by what both branches guarantee, here
-- a transmission, which each branch makes.

alternatives : R
alternatives = ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆

claimed-in-both-branches : [] ⊢C⦂ unit ! ⟅ ⌈ send ⌉ ⟆
claimed-in-both-branches =
  box alternatives (const 42)
                                     -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ ] Reading
    (if true
      `then coerce holds
              (perform read ⋆        -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (perform send (const 0)
                                     -- ⟨ ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- asking for the reading alone puts it out of the transmitting
-- branch's reach

sampling-branch-covers-it : 𝟏ᵣ ·ᵣ opTime read ≾ᵣ demand
sampling-branch-covers-it = holds

transmitting-branch-does-not : ¬ (𝟏ᵣ ·ᵣ opTime send ≾ᵣ demand)
transmitting-branch-does-not = fails

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing locks its continuation by the grade the first part is
-- typed at and binds that part's result: the `⟨ … ⟩ ∷ …` on the `⨟`
-- line below. What a `coerce` there forgets is not time but the
-- operation: a reading may be traded for the tick it took, and a box
-- asking for the reading is then out of reach.

claim-after-a-reading : [] ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-a-reading =
  box demand (const 42)              -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    ((perform read ⋆ (return here))
      ⨟                              -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- the coercion that trades the reading for its tick is available

trading-it-for-a-tick : opTime read ·ₑ 𝟏ₑ ≾ₑ ιₑ 1 ·ₑ 𝟏ₑ
trading-it-for-a-tick = holds

-- and taking it makes the lock `⟨ ⟅ ⟨ 1 ⟩ ⟆ ⟩`, which covers no
-- reading, so the box is closed

forgetting-the-reading-closes-it : ¬ (𝟏ᵣ ·ᵣ ιᵣ 1 ≾ᵣ demand)
forgetting-the-reading-closes-it = fails

------------------------------------------------------------------------
-- Non-singleton grades
--
-- A grade with several members is read disjunctively: each run of the
-- computation covers one of them. `if` produces one, its grade being
-- the union of its branches'. An `unbox` after the join is discharged
-- only if every branch discharges it.

-- the grade of the conditional: the join of what its branches
-- guarantee, which is their union

after-the-join : E
after-the-join = ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆

-- and the grade on the box, a different element of the same monoid: it
-- asks for a reading or for two ticks, and the two branches meet it
-- by different members: the sampling branch covers the reading and
-- not the ticks, the storing branch the other way round.

mixed-demand : R
mixed-demand = ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆

storing-branch-takes-the-ticks : 𝟏ᵣ ·ᵣ opTime write ≾ᵣ ⟅ ⟨ 2 ⟩ ⟆
storing-branch-takes-the-ticks = holds

storing-branch-not-the-reading : ¬ (𝟏ᵣ ·ᵣ opTime write ≾ᵣ demand)
storing-branch-not-the-reading = fails

claim-after-a-branch :
  [] ∷ bool ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-a-branch =
  box mixed-demand (const 42)
                                     -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    ((if eternal-var boolₑ (Tl-∷ Hd)
        `then coerce {ε' = after-the-join} holds (perform read ⋆ (return ⋆))
        `else coerce holds (perform write (const 0) (return ⋆)))
      ⨟                              -- ⟨ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- both of the box's members are needed, one for each branch: dropping
-- either closes it

the-reading-alone : ¬ (𝟏ᵣ ·ᵣ after-the-join ≾ᵣ demand)
the-reading-alone = fails

the-ticks-alone : ¬ (𝟏ᵣ ·ᵣ after-the-join ≾ᵣ ⟅ ⟨ 2 ⟩ ⟆)
the-ticks-alone = fails

-- a box with one member does survive the join when both branches reach
-- that member: a tick is spent either way

a-tick-either-way : 𝟏ᵣ ·ᵣ after-the-join ≾ᵣ ⟅ ⟨ 1 ⟩ ⟆
a-tick-either-way = holds

-- Nesting the conditionals gives a grade with three members, and the
-- three runs have nothing in common but the tick they each spend. So a
-- box asking for a tick survives both joins, and one asking for two
-- does not: the sampling branch spends only one.

three-ways : E
three-ways = ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆

sampling-branch-joins : opTime read ·ₑ 𝟏ₑ ≾ₑ three-ways
sampling-branch-joins = holds

storing-branch-joins : opTime write ·ₑ 𝟏ₑ ≾ₑ three-ways
storing-branch-joins = holds

claim-after-three-ways :
  [] ∷ bool ⊢C⦂ unit ! ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉
                       ∣ ⌈ write ⌉ ∙ ⌈ send ⌉
                       ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-three-ways =
  box ⟅ ⟨ 1 ⟩ ⟆ (const 42)           -- ∷ [ ⟅ ⟨ 1 ⟩ ⟆ ] Reading
    ((if eternal-var boolₑ (Tl-∷ Hd)
        `then coerce {ε' = three-ways} holds (perform read ⋆ (return ⋆))
        `else (if eternal-var boolₑ (Tl-∷ Hd)
                `then coerce holds (perform write (const 0) (return ⋆))
                `else coerce holds (perform send (const 0) (return ⋆))))
      ⨟                              -- ⟨ three-ways ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- two ticks are more than the sampling branch spends, so a box asking
-- for them does not survive the joins

two-ticks-do-not : ¬ (𝟏ᵣ ·ᵣ three-ways ≾ᵣ ⟅ ⟨ 2 ⟩ ⟆)
two-ticks-do-not = fails

------------------------------------------------------------------------
-- Programs written at these guarantees
--
-- A box asking for two ticks' worth of work, claimed on both sides of
-- an `if`: one branch stores a reading, which is certain of two ticks,
-- and the other idles for two. Both then transmit, so both guarantee
-- six ticks, and that is the conditional's grade.

two-ticks : R
two-ticks = ⟅ ⟨ 2 ⟩ ⟆

work-or-wait : [] ∷ bool ⊢C⦂ unit ! ⟅ ⟨ 6 ⟩ ⟆
work-or-wait =
  box two-ticks (const 42)           -- ∷ [ ⟅ ⟨ 2 ⟩ ⟆ ] Reading
    (if eternal-var boolₑ (Tl-∷ Hd)
      `then coerce holds
              (perform write (const 0)
                                     -- ⟨ ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (delay 2               -- ⟨ ⟅ ⟨ 2 ⟩ ⟆ ⟩
                (unbox (Tl-⟨⟩ Hd) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- seven ticks are more than either branch guarantees

seven-ticks-not-guaranteed :
  ¬ (opTime write ·ₑ (opTime send ·ₑ 𝟏ₑ) ≾ₑ ⟅ ⟨ 7 ⟩ ⟆)
seven-ticks-not-guaranteed = fails

-- and a branch that only takes a reading would not cover the box: one
-- tick against the two it asks for

sampling-branch-too-little : ¬ (𝟏ᵣ ·ᵣ opTime read ≾ᵣ two-ticks)
sampling-branch-too-little = fails

------------------------------------------------------------------------
-- Effect handling
--
-- Handling locks its `in` part by the handled computation's grade, as
-- sequencing does.

forwarded : [] ⊢C⦂ Reading ! ⟅ ⌈ read ⌉ ⟆
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ! ⟅ ⌈ read ⌉ ⟆
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: it is graded by a guarantee that
-- names the operation, and returning at once covers nothing

no-discarding : ¬ (𝟏ₑ ≾ₑ op-grade read ·ₑ 𝟏ₑ)
no-discarding = failsᵉ 𝟏ₑ (op-grade read ·ₑ 𝟏ₑ)
