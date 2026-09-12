------------------------------------------------------------------------
-- Typed example computations at the grade of trace guarantees.        --
--                                                                     --
-- Effect grades and resource grades are both sets of timed traces at   --
-- the coverage order, and each operation is graded by the one-event    --
-- run that performs it. A grade lists guarantees, and a computation    --
-- sits below it when each of its runs *covers* one of them: every      --
-- operation the guarantee names has occurred, and every delay it names --
-- has been paid out of the run's own time, operations counted at       --
-- `costˡᵒ` -- read 1, write 2, send 4 -- since that is all each is     --
-- certain to take.                                                     --
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
--                                                                     --
-- The comments inside the programs say what each former appends to the --
-- context its subcomputation is typed in: `⟨ ρ ⟩` a lock, `∷ A` a      --
-- binding. Here a lock records which operation ran, not merely that    --
-- time passed, and it is the product of the locks between a box's      --
-- binding and its `unbox` that the premise weighs against the box.     --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Timed.LeftSided where

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_; costˡᵒ;
         NeTraces; traces; ε; _∙_; ⌈_⌉; ⟨_⟩; ⟅_⟆; ⟅_∣_⟆; ⟅_∣_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
  using (left-sided; holds; fails; failsᵉ)

open import Syntax.Grades.Traces.Coverage.AsOrder Op _≟ₒ_ costˡᵒ
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
sampling =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform write here              -- ⟨ ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
relaying =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform send here               -- ⟨ ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
tagged-relaying =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

-- a computation that only idles, which guarantees time and no work

idling : [] ⊢C⦂ Unit ‼ ⟅ ⟨ 5 ⟩ ⟆
idling =
  delay 5                            -- ⟨ ⟅ ⟨ 5 ⟩ ⟆ ⟩
    (return ⋆)

------------------------------------------------------------------------
-- Nothing goes stale
--
-- `var`'s bound is `ρ ≾ᵣ uᵣ`, and every run covers the empty
-- guarantee, so a reading survives whatever locks stand over it.

nothing-goes-stale : (ρ : R) → ρ ≾ᵣ uᵣ
nothing-goes-stale ρ = u-≽ˢ (traces ρ)

-- take a reading, idle two ticks, and transmit the reading taken
-- before the idling

idle-then-transmit : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
idle-then-transmit =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (delay 2                         -- ⟨ ⟅ ⟨ 2 ⟩ ⟆ ⟩
      (perform send (fresh-var (nothing-goes-stale _) (Tl-⟨⟩ Hd))
                                     -- ⟨ ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
        (return ⋆)))

carried-reading : [] ∷ Reading ⊢C⦂ Reading ‼ ⟅ ⌈ read ⌉ ⟆
carried-reading =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (fresh-var (nothing-goes-stale _) (Tl-∷ (Tl-⟨⟩ Hd))))

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves up the order, and up means "guarantees less": a run
-- may forget the operations it performed, or trade them for the time
-- they took. The context is untouched.

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
-- the two branches are both bound to spend. Neither branch locks the
-- context.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

timed-branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ⟅ ⟨ 2 ⟩ ⟆
timed-branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

-- three ticks are more than the storing branch guarantees, being the
-- store's worst case rather than its best

three-ticks-not-guaranteed : ¬ (opTime write ·ₑ uₑ ≾ₑ ⟅ ⟨ 3 ⟩ ⟆)
three-ticks-not-guaranteed = fails

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
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (if true
      `then coerce holds (perform send  here (return ⋆))
      `else coerce holds (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a resource that comes due when work has been done
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`: what the computation did between
-- boxing the resource and claiming it -- the locks the comments show --
-- has to cover what the box asks for. The box below asks for a reading.

demand : R
demand = ⟅ ⌈ read ⌉ ⟆

-- the run stores the reading as well before claiming, so the premise
-- is not an equality: `⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆` covers the demand for
-- a reading with the store left over

claim-after-storing : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-storing =
  box {ρ = demand} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (perform read ⋆                  -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (perform write here            -- ⟨ ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) holds
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

handed-over : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box {ρ = demand} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (lam                             -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
       (perform read ⋆               -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

-- and the claim survives extra work in between: two readings cover a
-- demand for one, so the function may sample again before claiming
-- what it was handed. Two locks stand between the binding and the
-- claim, and their product is `⟅ ⌈ read ⌉ ∙ ⌈ read ⌉ ⟆`.

handed-over' : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over' =
  box {ρ = demand} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (lam                             -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
       (perform read ⋆               -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (perform read ⋆             -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
           (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) holds
                                     -- ∷ Reading
             (perform send here (return ⋆)))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box {ρ = demand} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    (perform read ⋆                  -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds -- ∷ Reading
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- idling does not discharge a demand for a reading, however long it
-- goes on

idling-does-not-discharge-it : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ demand)
idling-does-not-discharge-it = fails

-- and neither does doing nothing at all: with no lock in between there
-- is nothing to cover the demand with

claiming-at-once : ¬ (uᵣ ≾ᵣ demand)
claiming-at-once = failsᵉ uᵣ demand

-- a demand for *time* is discharged by anything that takes it, work
-- included: two ticks of idling, or a store, both cover two ticks

waiting : R
waiting = ⟅ ⟨ 2 ⟩ ⟆

claim-after-idling : [] ⊢C⦂ Unit ‼ ⟅ ⟨ 3 ⟩ ∙ ⌈ send ⌉ ⟆
claim-after-idling =
  box {ρ = waiting} (const 42)       -- ∷ [ ⟅ ⟨ 2 ⟩ ⟆ ] Reading
    (delay 3                         -- ⟨ ⟅ ⟨ 3 ⟩ ⟆ ⟩
      (unbox (Tl-⟨⟩ Hd) holds        -- ∷ Reading
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
                                     -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ ] Reading
    (if true
      `then coerce holds
              (perform read ⋆        -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (perform send (const 0)
                                     -- ⟨ ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- asking for the reading alone puts it out of the transmitting
-- branch's reach

sampling-branch-covers-it : uᵣ ·ᵣ opTime read ≾ᵣ demand
sampling-branch-covers-it = holds

transmitting-branch-does-not : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ demand)
transmitting-branch-does-not = fails

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing locks its continuation by the grade the first part is
-- *typed at* and binds that part's result -- the `⟨ … ⟩ ∷ …` on the
-- `⨟` line below. So a `coerce` on the first part changes the lock, and
-- can only take claims away, which is `coercion-only-closes`. What a
-- coercion forgets here is not time but the operation: a reading may be
-- traded for the tick it took, and a box asking for the reading is then
-- out of reach.

claim-after-a-reading : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-a-reading =
  box {ρ = demand} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ⟆ ] Reading
    ((perform read ⋆ (return here))
      ⨟                              -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- the coercion that trades the reading for its tick is available

trading-it-for-a-tick : opTime read ·ₑ uₑ ≾ₑ of-natᵉ 1 ·ₑ uₑ
trading-it-for-a-tick = holds

-- and taking it makes the lock `⟨ ⟅ ⟨ 1 ⟩ ⟆ ⟩`, which covers no
-- reading, so the box is closed

forgetting-the-reading-closes-it : ¬ (uᵣ ·ᵣ of-natʳ 1 ≾ᵣ demand)
forgetting-the-reading-closes-it = fails

------------------------------------------------------------------------
-- Non-singleton grades
--
-- A grade with several members is read disjunctively: each run of the
-- computation covers one of them. `if` is what produces one, its grade
-- being the join of the branches' and the union being that join. And
-- sequencing after the join locks its continuation by the union, so an
-- `unbox` there is discharged only if *every* branch discharges it --
-- the condition being universal in the elapsed set and existential in
-- the box's.

-- the grade of the conditional: the join of what its branches
-- guarantee, which is their union

after-the-join : E
after-the-join = ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆

-- and the grade on the box, which is a different element of the same
-- monoid -- the two are the same carrier only because the grade system
-- is the identity one, and they are doing different jobs. This one asks
-- for a reading *or* for two ticks, and the two branches meet it by
-- different members: the sampling branch covers the reading and cannot
-- cover the ticks (`sampling-branch-covers-it`,
-- `sampling-branch-too-little`), the storing branch the other way
-- round.

mixed-demand : R
mixed-demand = ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆

storing-branch-takes-the-ticks : uᵣ ·ᵣ opTime write ≾ᵣ ⟅ ⟨ 2 ⟩ ⟆
storing-branch-takes-the-ticks = holds

storing-branch-not-the-reading : ¬ (uᵣ ·ᵣ opTime write ≾ᵣ demand)
storing-branch-not-the-reading = fails

claim-after-a-branch :
  [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-a-branch =
  box {ρ = mixed-demand} (const 42)
                                     -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    ((if eternal-var Boolₑ (Tl-∷ Hd)
        `then coerce {ε' = after-the-join} holds (perform read ⋆ (return ⋆))
        `else coerce holds (perform write (const 0) (return ⋆)))
      ⨟                              -- ⟨ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- both of the box's members are needed, one for each branch: dropping
-- either closes it

the-reading-alone : ¬ (uᵣ ·ᵣ after-the-join ≾ᵣ demand)
the-reading-alone = fails

the-ticks-alone : ¬ (uᵣ ·ᵣ after-the-join ≾ᵣ ⟅ ⟨ 2 ⟩ ⟆)
the-ticks-alone = fails

-- a box with one member does survive the join when both branches reach
-- that member: a tick is spent either way

a-tick-either-way : uᵣ ·ᵣ after-the-join ≾ᵣ ⟅ ⟨ 1 ⟩ ⟆
a-tick-either-way = holds

-- Nesting the conditionals gives a grade with three members, and the
-- three runs have nothing in common but the tick they each spend. So a
-- box asking for a tick survives both joins, and one asking for two
-- does not: the sampling branch spends only one.

three-ways : E
three-ways = ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆

sampling-branch-joins : opTime read ·ₑ uₑ ≾ₑ three-ways
sampling-branch-joins = holds

storing-branch-joins : opTime write ·ₑ uₑ ≾ₑ three-ways
storing-branch-joins = holds

claim-after-three-ways :
  [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉
                       ∣ ⌈ write ⌉ ∙ ⌈ send ⌉
                       ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-three-ways =
  box {ρ = ⟅ ⟨ 1 ⟩ ⟆} (const 42)     -- ∷ [ ⟅ ⟨ 1 ⟩ ⟆ ] Reading
    ((if eternal-var Boolₑ (Tl-∷ Hd)
        `then coerce {ε' = three-ways} holds (perform read ⋆ (return ⋆))
        `else (if eternal-var Boolₑ (Tl-∷ Hd)
                `then coerce holds (perform write (const 0) (return ⋆))
                `else coerce holds (perform send (const 0) (return ⋆))))
      ⨟                              -- ⟨ three-ways ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- two ticks are more than the sampling branch spends, so a box asking
-- for them does not survive the joins

two-ticks-do-not : ¬ (uᵣ ·ᵣ three-ways ≾ᵣ ⟅ ⟨ 2 ⟩ ⟆)
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

work-or-wait : [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⟨ 6 ⟩ ⟆
work-or-wait =
  box {ρ = two-ticks} (const 42)     -- ∷ [ ⟅ ⟨ 2 ⟩ ⟆ ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce holds
              (perform write (const 0)
                                     -- ⟨ ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (delay 2               -- ⟨ ⟅ ⟨ 2 ⟩ ⟆ ⟩
                (unbox (Tl-⟨⟩ Hd) holds
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- seven ticks are more than either branch guarantees

seven-ticks-not-guaranteed :
  ¬ (opTime write ·ₑ (opTime send ·ₑ uₑ) ≾ₑ ⟅ ⟨ 7 ⟩ ⟆)
seven-ticks-not-guaranteed = fails

-- and a branch that only takes a reading would not cover the box: one
-- tick against the two it asks for

sampling-branch-too-little : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ two-ticks)
sampling-branch-too-little = fails

------------------------------------------------------------------------
-- Effect handling
--
-- Handling locks its `in` part by the handled computation's grade,
-- exactly as sequencing does.

forwarded : [] ⊢C⦂ Reading ‼ ⟅ ⌈ read ⌉ ⟆
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ ⟅ ⌈ read ⌉ ⟆
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: it is graded by a guarantee that
-- names the operation, and returning at once covers nothing

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = failsᵉ uₑ (op-grade read ·ₑ uₑ)
