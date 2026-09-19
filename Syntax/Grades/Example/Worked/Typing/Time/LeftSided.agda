------------------------------------------------------------------------
-- Typed example computations at the grade of lower bounds.            --
--                                                                     --
-- Effect grades and resource grades are both `[ n ,+∞⟩`, "at least `n` --
-- time steps", and the operations are graded by the time they are      --
-- guaranteed to take: read 1, write 2, send 4.                        --
--                                                                     --
-- Read as an effect grade, `[ n ,+∞⟩` says a computation takes at      --
-- least `n` ticks, and `coerce` may forget how many. Read as a         --
-- resource grade it says at least `n` have passed, so `unbox`'s        --
-- premise `ρ' ≾ᵣ ρ` -- what elapsed is at least what the box asks for  --
-- -- makes `[ ρ ] A` a resource that becomes available once `ρ` has    --
-- gone by. A claim made too early is refused; there is no claim made   --
-- too late, because a lower bound records no deadline to overrun.      --
--                                                                     --
-- Two consequences of the grades being floors are worth naming, and    --
-- both are checked below:                                              --
--                                                                     --
--   * `var`'s bound `ρ ≾ᵣ uᵣ` holds at every `ρ`, so no variable ever  --
--     goes stale: what has passed is never a reason to lose data.     --
--                                                                     --
--   * a handler clause cannot drop its continuation. It is graded at   --
--     `op-grade op ·ₑ ε''`, and returning at once guarantees nothing,  --
--     so the coercion such a clause would need does not exist.         --
--                                                                     --
-- The comments inside the programs say what each former appends to the --
-- context its subcomputation is typed in: `⟨ ρ ⟩` a lock, `∷ A` a      --
-- binding. Reading them off downwards gives the context at any point,  --
-- and the locks between a box's binding and its `unbox` are what that  --
-- rule's premise compares against the box's own grade.                 --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Time.LeftSided where

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Time.LeftSided
  using (𝕀; [_,+∞⟩; left-sided-intervals)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send)

open import Syntax.Grades.Example.Worked.Time using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, graded by the time they are guaranteed to take

opTime : Op → 𝕀
opTime read  = [ 1 ,+∞⟩
opTime write = [ 2 ,+∞⟩
opTime send  = [ 4 ,+∞⟩

open import Syntax.Grades.Example.Worked.Typing.Core left-sided-intervals opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- A computation's grade is the sum of the grades of the operations
-- along it: the time the whole run is guaranteed to take. Each
-- `perform` locks the context by the operation's grade and binds its
-- result.

-- take a reading and hand it back

sampling : [] ⊢C⦂ Reading ‼ [ 1 ,+∞⟩
sampling =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (return here)

-- take a reading and store it

storing : [] ⊢C⦂ Unit ‼ [ 3 ,+∞⟩
storing =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (perform write here              -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ Unit
      (return ⋆))

-- take a reading and transmit it

relaying : [] ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
relaying =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (perform send here               -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ Unit
      (return ⋆))

-- take a reading, tag it with the node's identifier, and transmit the
-- reading back out of the pair; pairing costs no time, so the grade is
-- the one `relaying` has

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
tagged-relaying =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Nothing goes stale
--
-- `var` asks for `ρ ≾ᵣ uᵣ` at a non-eternal type, and every grade sits
-- below the unit here: a floor of `0` is what a bound forgetting
-- everything says. So a reading survives whatever passes.

nothing-goes-stale : (ρ : R) → ρ ≾ᵣ uᵣ
nothing-goes-stale [ n ,+∞⟩ = ≤!

-- take a reading, idle two ticks, and transmit the reading taken before
-- the idling. The reading is bound above two locks by the time it is
-- used, and `≤!` is `var`'s bound at their product.

idle-then-transmit : [] ⊢C⦂ Unit ‼ [ 7 ,+∞⟩
idle-then-transmit =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (delay 2                         -- ⟨ [ 2 ,+∞⟩ ⟩
      (perform send (fresh-var ≤! (Tl-⟨⟩ Hd))
                                     -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ Unit
        (return ⋆)))

-- the identifier crosses the reading's execution time because it is
-- eternal, and asks for no bound at all

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ [ 1 ,+∞⟩
carried-id =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

-- a reading crosses it because nothing goes stale

carried-reading : [] ∷ Reading ⊢C⦂ Reading ‼ [ 1 ,+∞⟩
carried-reading =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (return (fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves a computation up the order, and up means "guarantees
-- less". A guarantee may always be forgotten and never invented. It
-- leaves the context alone: only the grade moves.

forgetting-time : [] ⊢C⦂ Unit ‼ [ 2 ,+∞⟩
forgetting-time = coerce ≤! (perform read ⋆ (perform write here (return ⋆)))

inventing-time : ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ [ 4 ,+∞⟩)
inventing-time = ≰!

------------------------------------------------------------------------
-- Conditional branching
--
-- The two branches are typed at one grade, so both are coerced to it.
-- Here that grade is the *smaller* floor: a conditional guarantees only
-- what its faster branch does. Neither branch locks the context: both
-- start from the context the `if` itself is in.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ [ 2 ,+∞⟩
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce ≤! (perform send  here (return ⋆))
    `else coerce ≤! (perform write here (return ⋆))

-- the transmitting branch's own grade will not do for the conditional,
-- since the storing branch cannot claim four ticks

storing-guarantees-less : ¬ (opTime write ·ₑ uₑ ≾ₑ [ 4 ,+∞⟩)
storing-guarantees-less = ≰!

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

either-reading : [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ [ 4 ,+∞⟩
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

-- branching on data that an operation produced: the scrutinee is bound
-- by the `perform`, so the `if` sits under its lock

sampling-then-branching : [] ⊢C⦂ Unit ‼ [ 3 ,+∞⟩
sampling-then-branching =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (if true
      `then coerce ≤! (perform send  here (return ⋆))
      `else coerce ≤! (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a resource that becomes available
--
-- `unbox`'s premise `elapsed ≾ᵣ ρ` reads `ρ ≤ elapsed` here: the box
-- may be claimed once at least as much time has passed as it asks for.
-- What has elapsed is the product of the locks standing between the
-- box's binding and the claim -- the `⟨ … ⟩` entries the comments
-- show.

-- a reading promised in two ticks, claimed after idling three: the
-- premise is `2 ≤ 3`, and waiting longer than the box asks for is
-- always allowed

claim-after-idling : [] ⊢C⦂ Unit ‼ [ 7 ,+∞⟩
claim-after-idling =
  box {ρ = [ 2 ,+∞⟩} (const 42)      -- ∷ [ [ 2 ,+∞⟩ ] Reading
    (delay 3                         -- ⟨ [ 3 ,+∞⟩ ⟩
      (unbox (Tl-⟨⟩ Hd) ≤!           -- ∷ Reading
        (perform send here (return ⋆))))

-- taking a reading is one tick's worth of waiting, which is not enough
-- for that box

claim-after-sampling-fails : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ [ 2 ,+∞⟩)
claim-after-sampling-fails = ≰!

-- and claiming it at once is not enough either

claim-at-once-fails : ¬ (uᵣ ≾ᵣ [ 2 ,+∞⟩)
claim-at-once-fails = ≰!

-- a resource promised in one tick is claimable after a reading, since
-- performing an operation is how time passes. The premise is an
-- equality: the reading takes exactly the tick the box asks for.

claim-after-sampling : [] ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
claim-after-sampling =
  box {ρ = [ 1 ,+∞⟩} (const 42)      -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (perform read ⋆                  -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!    -- ∷ Reading
        (perform send here (return ⋆))))

-- a resource claimable with nothing elapsed is one that promises
-- nothing: `uᵣ ≾ᵣ ρ` forces the box's grade to the unit, there being no
-- lock between the binding and the claim

claiming-now : [] ⊢C⦂ Unit ‼ [ 4 ,+∞⟩
claiming-now =
  box {ρ = [ 0 ,+∞⟩} (const 42)      -- ∷ [ [ 0 ,+∞⟩ ] Reading
    (unbox Hd ≤!                     -- ∷ Reading
      (perform send here (return ⋆)))

-- a boxed resource crosses a binder as an ordinary value: the function
-- takes the box, stores a reading of its own, and then claims it --
-- two ticks against the one the box asks for

handed-over : [] ⊢C⦂ Unit ‼ [ 6 ,+∞⟩
handed-over =
  box {ρ = [ 1 ,+∞⟩} (const 42)      -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (lam                             -- ∷ [ [ 1 ,+∞⟩ ] Reading
       (perform write (const 0)      -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ Unit
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- Each branch discharges the premise at what it has itself done, so the
-- same box can be within one branch's reach and out of the other's. A
-- resource promised in four ticks is claimable after a transmission and
-- not after a reading.

reachable-after-a-transmission : uᵣ ·ᵣ opTime send ≾ᵣ [ 4 ,+∞⟩
reachable-after-a-transmission = ≤!

unreachable-after-a-reading : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ [ 4 ,+∞⟩)
unreachable-after-a-reading = ≰!

-- promised in one tick instead, both branches reach it with time to
-- spare -- two ticks in one, four in the other -- and the conditional
-- is graded at the floor of the two

claimed-in-both-branches : [] ⊢C⦂ Unit ‼ [ 6 ,+∞⟩
claimed-in-both-branches =
  box {ρ = [ 1 ,+∞⟩} (const 42)      -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (if true
      `then coerce ≤!
              (perform write (const 0)
                                     -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce ≤!
              (perform send (const 0)
                                     -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- claiming the resource and then choosing what to transmit -- the
-- claimed reading or one taken along the way -- with both branches
-- making the same run

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ [ 6 ,+∞⟩
either-way =
  box {ρ = [ 1 ,+∞⟩} (const 42)      -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (perform read ⋆                  -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (delay 1                       -- ⟨ [ 1 ,+∞⟩ ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤!
                                     -- ∷ Reading
          (if eternal-var Boolₑ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))
            `then perform send here (return ⋆)
            `else perform send (fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd))) (return ⋆)))))

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing locks its continuation by the grade the first part is
-- *typed at* and binds that part's result -- the `⟨ … ⟩ ∷ …` on the
-- `⨟` line below. A `coerce` on the first part therefore changes the
-- lock, and at these grades can only take claims away: coercing
-- forgets time, and time is what the box is compared against.

-- a reading and a store guarantee three ticks, exactly what the box
-- asks for, so the claim has no slack to survive a coercion

claim-after-a-store : [] ⊢C⦂ Unit ‼ [ 7 ,+∞⟩
claim-after-a-store =
  box {ρ = [ 3 ,+∞⟩} (const 42)      -- ∷ [ [ 3 ,+∞⟩ ] Reading
    ((perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 3 ,+∞⟩ ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!   -- ∷ Reading
          (perform send here (return ⋆)))

-- forgetting one of those ticks first puts the box out of reach: the
-- lock the continuation is typed under is the coerced grade

coercing-closes-it : ¬ (uᵣ ·ᵣ [ 2 ,+∞⟩ ≾ᵣ [ 3 ,+∞⟩)
coercing-closes-it = ≰!

-- the same program with the coercion, claiming a box that asks for no
-- more than the coerced grade guarantees

claim-after-a-coerced-store : [] ⊢C⦂ Unit ‼ [ 6 ,+∞⟩
claim-after-a-coerced-store =
  box {ρ = [ 2 ,+∞⟩} (const 42)      -- ∷ [ [ 2 ,+∞⟩ ] Reading
    (coerce {ε' = [ 2 ,+∞⟩} ≤!
       (perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!   -- ∷ Reading
          (perform send here (return ⋆)))

-- and that box was within the uncoerced program's reach as well, which
-- is the direction `coercion-only-closes` gives at every grade

claim-without-coercing : uᵣ ·ᵣ [ 3 ,+∞⟩ ≾ᵣ [ 2 ,+∞⟩
claim-without-coercing = ≤!

------------------------------------------------------------------------
-- Joining branches, and what survives the join
--
-- A conditional's grade is the join of its branches', which at these
-- intervals is the smaller floor. Sequencing after it locks the
-- continuation by that join, so a box claimed there has to have been
-- discharged by *both* branches.

-- the conditional guarantees two ticks, and the box asks for one, so
-- the claim goes through with a tick to spare

claim-after-a-branch : [] ∷ Bool ⊢C⦂ Unit ‼ [ 6 ,+∞⟩
claim-after-a-branch =
  box {ρ = [ 1 ,+∞⟩} (const 42)      -- ∷ [ [ 1 ,+∞⟩ ] Reading
    ((if eternal-var Boolₑ (Tl-∷ Hd)
        `then coerce {ε' = [ 2 ,+∞⟩} ≤! (perform send (const 0) (return ⋆))
        `else delay 2 (return ⋆))
      ⨟                              -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!   -- ∷ Reading
          (perform send here (return ⋆)))

-- the transmitting branch guarantees four ticks on its own -- that is
-- `reachable-after-a-transmission` above -- and the join loses them to
-- the branch that only idles

four-ticks-lost-at-the-join : ¬ (uᵣ ·ᵣ [ 2 ,+∞⟩ ≾ᵣ [ 4 ,+∞⟩)
four-ticks-lost-at-the-join = ≰!

------------------------------------------------------------------------
-- Programs written at these intervals
--
-- A lower bound counts time and nothing else. The two runs below reach
-- the same resource, one by working and one by waiting, the locks
-- between binding and claim multiplying to `[ 5 ,+∞⟩` either way.

-- a resource promised in four ticks, reached by working: a reading and
-- a store are three ticks, and two of idling make five, a tick more
-- than the box asks for

duty-cycle : [] ⊢C⦂ Unit ‼ [ 9 ,+∞⟩
duty-cycle =
  box {ρ = [ 4 ,+∞⟩} (const 42)      -- ∷ [ [ 4 ,+∞⟩ ] Reading
    (perform read ⋆                  -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (perform write here            -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ Unit
        (delay 2                     -- ⟨ [ 2 ,+∞⟩ ⟩
          (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))) ≤!
                                     -- ∷ Reading
            (perform send here (return ⋆))))))

-- the same resource, reached by idling instead

waiting-instead : [] ⊢C⦂ Unit ‼ [ 9 ,+∞⟩
waiting-instead =
  box {ρ = [ 4 ,+∞⟩} (const 42)      -- ∷ [ [ 4 ,+∞⟩ ] Reading
    (delay 5                         -- ⟨ [ 5 ,+∞⟩ ⟩
      (unbox (Tl-⟨⟩ Hd) ≤!           -- ∷ Reading
        (perform send here (return ⋆))))

-- one tick short of it, the claim is refused: dropping the store from
-- `duty-cycle` leaves three ticks against a resource promised in four

one-tick-short : ¬ (uᵣ ·ᵣ opTime read ·ᵣ of-natʳ 2 ≾ᵣ [ 4 ,+∞⟩)
one-tick-short = ≰!

-- two resources on different schedules, claimed at the two points of
-- one run where each has come due: the first after a reading and a
-- store, the second after transmitting as well. Two box bindings stand
-- in the context, and the indices tell them apart. Neither premise is
-- an equality: three ticks have passed against a promise of two, and
-- seven against a promise of six.

two-schedules : [] ⊢C⦂ Unit ‼ [ 11 ,+∞⟩
two-schedules =
  box {ρ = [ 2 ,+∞⟩} (const 1)       -- ∷ [ [ 2 ,+∞⟩ ] Reading
    (box {ρ = [ 6 ,+∞⟩} (const 2)    -- ∷ [ [ 6 ,+∞⟩ ] Reading
      (perform read ⋆                -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
        (perform write here          -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ Unit
          (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))) ≤!
                                     -- ∷ Reading
            (perform send here       -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ Unit
              (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))))))
                     ≤!
                                     -- ∷ Reading
                (perform send here (return ⋆))))))))

-- and the later one is out of reach at the earlier point

not-due-yet : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ [ 6 ,+∞⟩)
not-due-yet = ≰!

-- a resource promised in three ticks, claimed on both sides of an
-- `if`: transmitting takes four outright, while taking a reading takes
-- one and has to be followed by three of idling. The two branches reach
-- the same floor, so the conditional needs no coercion at all, and each
-- passes the premise with a tick to spare.

scheduled-choice : [] ∷ Bool ⊢C⦂ Unit ‼ [ 8 ,+∞⟩
scheduled-choice =
  box {ρ = [ 3 ,+∞⟩} (const 42)      -- ∷ [ [ 3 ,+∞⟩ ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then perform send (const 0)   -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ Unit
              (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                                     -- ∷ Reading
                (perform send here (return ⋆)))
      `else perform read ⋆           -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
              (delay 3               -- ⟨ [ 3 ,+∞⟩ ⟩
                (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤!
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- without the idling the sampling branch would be two ticks short

------------------------------------------------------------------------
-- Effect handling
--
-- The forwarding clause performs the operation again and resumes, so it
-- spends exactly the grade it is typed at. Handling locks its `in` part
-- by the handled computation's grade, exactly as sequencing does.

forwarded : [] ⊢C⦂ Reading ‼ [ 1 ,+∞⟩
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (return here)

-- and a clause may reach an eternal binding across the barrier lock, use
-- its continuation, and answer with what it reached

identified : Node ⊢C⦂ NodeId ‼ [ 1 ,+∞⟩
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- what no clause can do here is drop its continuation: it is graded at
-- the operation's own time and a `return` guarantees none of it

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = ≰!

------------------------------------------------------------------------
-- The greatest grade
--
-- Here it is the unit: "at least 0 ticks" claims nothing, so every
-- grade weakens to it and a lock at `⊤ᵣ` lets everything through --
-- nothing ever expires under a lower bound.

everything-weakens : (ε : E) → ε ≾ₑ ⊤ₑ
everything-weakens = ≾-⊤ₑ

reading-survives-⊤ : ⊤ᵣ ≾ᵣ uᵣ
reading-survives-⊤ = ≤!

-- so a handler clause may close over a reading: `var`'s bound holds at
-- the barrier and at whatever the clause spends past it

reading-crosses-the-barrier :
  (op : Op) → (ε'' : E) → uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ uᵣ
reading-crosses-the-barrier op ε'' = nothing-goes-stale _

-- the node's reading, answered from inside a clause that performs the
-- operation again and resumes first

reported : Node ⊢C⦂ Reading ‼ [ 1 ,+∞⟩
reported =
  handle perform read ⋆ (return here)
    `with reporting reading-crosses-the-barrier
    `in                              -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (return here)
