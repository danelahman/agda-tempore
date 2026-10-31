------------------------------------------------------------------------
-- Typed example computations at the grade of lower bounds.           --
--                                                                    --
-- Effect grades and resource grades are both `[ n ,+∞⟩`, "at least   --
-- `n` time steps", and the operations are graded by the time they    --
-- are guaranteed to take: read 1, write 2, send 4.                   --
--                                                                    --
-- As an effect grade, `[ n ,+∞⟩` states that a computation takes at  --
-- least `n` ticks, and `coerce` may decrease `n`. As a resource      --
-- grade it states that at least `n` ticks have passed, so the        --
-- premise `ρ' ≾ᵣ ρ` of `unbox` (the elapsed grade is at least the    --
-- grade of the box) makes `[ ρ ] A` a resource that becomes          --
-- available once `ρ` has passed. A claim made too early is refused;  --
-- a lower bound imposes no deadline, and no claim is too late.       --
--                                                                    --
-- Two consequences of the grades being lower bounds, both checked    --
-- below:                                                             --
--                                                                    --
--   * the bound `ρ ≾ᵣ 𝟏ᵣ` of `var` holds at every `ρ`, so no         --
--     variable goes stale.                                           --
--                                                                    --
--   * a handler clause cannot discard its continuation. It is graded --
--     at `op-grade op ·ₑ ε''`, and returning at once guarantees      --
--     nothing, so the required coercion does not exist.              --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. Read downwards, they give the context at any      --
-- point, and the locks between the binding of a box and its `unbox`  --
-- are what the premise of that rule compares with the grade of the   --
-- box.                                                               --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Time.LeftSided where

open import Relation.Nullary using (¬_)

open import Grades.Examples.Time.LeftSided
  using (𝕀; [_,+∞⟩; left-sided-intervals)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, graded by the time they are guaranteed to take

open import Grades.Examples.Worked.Operations.Grading using (module Time-LeftSided)
open Time-LeftSided using (opTime) public

open import MonomorphicCalculus.Examples.Typing.Core left-sided-intervals opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- A computation's grade is the sum of the grades of the operations
-- along it: the time the whole run is guaranteed to take. Each
-- `perform` locks the context by the operation's grade and binds its
-- result.

-- take a reading and hand it back

sampling : [] ⊢ᶜ⦂ Reading ! [ 1 ,+∞⟩
sampling =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (return here)

-- take a reading and store it

storing : [] ⊢ᶜ⦂ unit ! [ 3 ,+∞⟩
storing =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (perform write here              -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ unit
      (return ⋆))

-- take a reading and transmit it

relaying : [] ⊢ᶜ⦂ unit ! [ 5 ,+∞⟩
relaying =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (perform send here               -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ unit
      (return ⋆))

-- take a reading, tag it with the node's identifier, and transmit the
-- reading back out of the pair; pairing costs no time, so the grade is
-- the one `relaying` has

tagged-relaying : [] ∷ NodeId ⊢ᶜ⦂ unit ! [ 5 ,+∞⟩
tagged-relaying =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `with perform send here (return ⋆))

------------------------------------------------------------------------
-- Nothing goes stale
--
-- `var` asks for `ρ ≾ᵣ 𝟏ᵣ` at a non-eternal type, and every grade sits
-- below the unit here: a floor of `0` is what a bound forgetting
-- everything says. So a reading survives whatever passes.

nothing-goes-stale : (ρ : R) → ρ ≾ᵣ 𝟏ᵣ
nothing-goes-stale [ n ,+∞⟩ = ≤!

-- take a reading, idle two ticks, and transmit the reading taken before
-- the idling. The reading is bound above two locks by the time it is
-- used, and `≤!` is `var`'s bound at their product.

idle-then-transmit : [] ⊢ᶜ⦂ unit ! [ 7 ,+∞⟩
idle-then-transmit =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (delay 2                         -- ⟨ [ 2 ,+∞⟩ ⟩
      (perform send (fresh-var ≤! (Tl-⟨⟩ Hd))
                                     -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ unit
        (return ⋆)))

-- the identifier crosses the reading's execution time because it is
-- eternal, and asks for no bound at all

carried-id : [] ∷ NodeId ⊢ᶜ⦂ NodeId ! [ 1 ,+∞⟩
carried-id =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

-- a reading crosses it because nothing goes stale

carried-reading : [] ∷ Reading ⊢ᶜ⦂ Reading ! [ 1 ,+∞⟩
carried-reading =
  perform read ⋆                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
    (return (fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves a computation up the order, and up means "guarantees
-- less". A guarantee may always be forgotten and never invented. It
-- leaves the context alone: only the grade moves.

forgetting-time : [] ⊢ᶜ⦂ unit ! [ 2 ,+∞⟩
forgetting-time = coerce ≤! (perform read ⋆ (perform write here (return ⋆)))

inventing-time : ¬ (opTime read ·ₑ (opTime write ·ₑ 𝟏ₑ) ≾ₑ [ 4 ,+∞⟩)
inventing-time = ≰!

------------------------------------------------------------------------
-- Conditional branching
--
-- The two branches are typed at one grade, so both are coerced to it.
-- That grade is the smaller floor: a conditional guarantees only
-- what its faster branch does. Neither branch locks the context: both
-- start from the context the `if` itself is in.

branching : [] ∷ bool ∷ Reading ⊢ᶜ⦂ unit ! [ 2 ,+∞⟩
branching =
  if eternal-var boolₑ (Tl-∷ Hd)
    `then coerce ≤! (perform send  here (return ⋆))
    `else coerce ≤! (perform write here (return ⋆))

-- the transmitting branch's own grade will not do for the conditional,
-- since the storing branch cannot claim four ticks

storing-guarantees-less : ¬ (opTime write ·ₑ 𝟏ₑ ≾ₑ [ 4 ,+∞⟩)
storing-guarantees-less = ≰!

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

either-reading : [] ∷ bool ∷ Reading ∷ Reading ⊢ᶜ⦂ unit ! [ 4 ,+∞⟩
either-reading =
  if eternal-var boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

-- branching on data that an operation produced: the scrutinee is bound
-- by the `perform`, so the `if` sits under its lock

sampling-then-branching : [] ⊢ᶜ⦂ unit ! [ 3 ,+∞⟩
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
-- box's binding and the claim: the `⟨ … ⟩` entries the comments show.

-- a reading promised in two ticks, claimed after idling three: the
-- premise is `2 ≤ 3`, and waiting longer than the box asks for is
-- always allowed

claim-after-idling : [] ⊢ᶜ⦂ unit ! [ 7 ,+∞⟩
claim-after-idling =
  box [ 2 ,+∞⟩ (const reading 42)    -- ∷ [ [ 2 ,+∞⟩ ] Reading
    (delay 3                         -- ⟨ [ 3 ,+∞⟩ ⟩
      (unbox (Tl-⟨⟩ Hd) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- taking a reading is one tick's worth of waiting, which is not enough
-- for that box

claim-after-sampling-fails : ¬ (𝟏ᵣ ·ᵣ opTime read ≾ᵣ [ 2 ,+∞⟩)
claim-after-sampling-fails = ≰!

-- and claiming it at once is not enough either

claim-at-once-fails : ¬ (𝟏ᵣ ≾ᵣ [ 2 ,+∞⟩)
claim-at-once-fails = ≰!

-- a resource promised in one tick is claimable after a reading, since
-- performing an operation is how time passes. The premise is an
-- equality: the reading takes exactly the tick the box asks for.

claim-after-sampling : [] ⊢ᶜ⦂ unit ! [ 5 ,+∞⟩
claim-after-sampling =
  box [ 1 ,+∞⟩ (const reading 42)    -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (perform read ⋆                  -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- a resource claimable with nothing elapsed is one that promises
-- nothing: `𝟏ᵣ ≾ᵣ ρ` forces the box's grade to the unit, there being no
-- lock between the binding and the claim

claiming-now : [] ⊢ᶜ⦂ unit ! [ 4 ,+∞⟩
claiming-now =
  box [ 0 ,+∞⟩ (const reading 42)    -- ∷ [ [ 0 ,+∞⟩ ] Reading
    (unbox Hd ≤! (<:ᵛ-refl _)        -- ∷ Reading
      (perform send here (return ⋆)))

-- a boxed resource crosses a binder as an ordinary value: the function
-- takes the box, stores a reading of its own, and then claims it, two
-- ticks against the one the box asks for

handed-over : [] ⊢ᶜ⦂ unit ! [ 6 ,+∞⟩
handed-over =
  box [ 1 ,+∞⟩ (const reading 42)       -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (fun                                -- ∷ [ [ 1 ,+∞⟩ ] Reading
       (perform write (const reading 0) -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ unit
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- Each branch discharges the premise at what it has itself done, so the
-- same box can be within one branch's reach and out of the other's. A
-- resource promised in four ticks is claimable after a transmission and
-- not after a reading.

reachable-after-a-transmission : 𝟏ᵣ ·ᵣ opTime send ≾ᵣ [ 4 ,+∞⟩
reachable-after-a-transmission = ≤!

unreachable-after-a-reading : ¬ (𝟏ᵣ ·ᵣ opTime read ≾ᵣ [ 4 ,+∞⟩)
unreachable-after-a-reading = ≰!

-- promised in one tick instead, both branches reach it with time to
-- spare (two ticks in one, four in the other), and the conditional
-- is graded at the floor of the two

claimed-in-both-branches : [] ⊢ᶜ⦂ unit ! [ 6 ,+∞⟩
claimed-in-both-branches =
  box [ 1 ,+∞⟩ (const reading 42)            -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (if true
      `then coerce ≤!
              (perform write (const reading 0)
                                     -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce ≤!
              (perform send (const reading 0)
                                     -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- claiming the resource and then choosing what to transmit (the
-- claimed reading or one taken along the way), with both branches
-- making the same run

either-way : [] ∷ bool ⊢ᶜ⦂ unit ! [ 6 ,+∞⟩
either-way =
  box [ 1 ,+∞⟩ (const reading 42)    -- ∷ [ [ 1 ,+∞⟩ ] Reading
    (perform read ⋆                  -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (delay 1                       -- ⟨ [ 1 ,+∞⟩ ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (if eternal-var boolₑ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))
            `then perform send here (return ⋆)
            `else perform send (fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd))) (return ⋆)))))

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing locks its continuation by the grade the first part is
-- typed at and binds that part's result: the `⟨ … ⟩ ∷ …` on the `⨟`
-- line below. A `coerce` on the first part therefore changes the
-- lock, and at these grades can only take claims away: coercing
-- forgets time, and time is what the box is compared against.

-- a reading and a store guarantee three ticks, exactly what the box
-- asks for, so the claim has no slack to survive a coercion

claim-after-a-store : [] ⊢ᶜ⦂ unit ! [ 7 ,+∞⟩
claim-after-a-store =
  box [ 3 ,+∞⟩ (const reading 42)            -- ∷ [ [ 3 ,+∞⟩ ] Reading
    ((perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 3 ,+∞⟩ ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- forgetting one of those ticks first puts the box out of reach: the
-- lock the continuation is typed under is the coerced grade

coercing-closes-it : ¬ (𝟏ᵣ ·ᵣ [ 2 ,+∞⟩ ≾ᵣ [ 3 ,+∞⟩)
coercing-closes-it = ≰!

-- the same program with the coercion, claiming a box that asks for no
-- more than the coerced grade guarantees

claim-after-a-coerced-store : [] ⊢ᶜ⦂ unit ! [ 6 ,+∞⟩
claim-after-a-coerced-store =
  box [ 2 ,+∞⟩ (const reading 42)            -- ∷ [ [ 2 ,+∞⟩ ] Reading
    (coerce {ε' = [ 2 ,+∞⟩} ≤!
       (perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- and that box was within the uncoerced program's reach as well, which
-- is the direction `coercion-only-closes` gives at every grade

claim-without-coercing : 𝟏ᵣ ·ᵣ [ 3 ,+∞⟩ ≾ᵣ [ 2 ,+∞⟩
claim-without-coercing = ≤!

------------------------------------------------------------------------
-- Joining branches, and what survives the join
--
-- A conditional's grade is the join of its branches', which at these
-- intervals is the smaller floor. Sequencing after it locks the
-- continuation by that join, so a box claimed there has to have been
-- discharged by both branches.

-- the conditional guarantees two ticks, and the box asks for one, so
-- the claim goes through with a tick to spare

claim-after-a-branch : [] ∷ bool ⊢ᶜ⦂ unit ! [ 6 ,+∞⟩
claim-after-a-branch =
  box [ 1 ,+∞⟩ (const reading 42)            -- ∷ [ [ 1 ,+∞⟩ ] Reading
    ((if eternal-var boolₑ (Tl-∷ Hd)
        `then coerce {ε' = [ 2 ,+∞⟩} ≤! (perform send (const reading 0) (return ⋆))
        `else delay 2 (return ⋆))
      ⨟                              -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- the transmitting branch guarantees four ticks on its own
-- (`reachable-after-a-transmission` above), and the join loses them to
-- the branch that only idles

four-ticks-lost-at-the-join : ¬ (𝟏ᵣ ·ᵣ [ 2 ,+∞⟩ ≾ᵣ [ 4 ,+∞⟩)
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

duty-cycle : [] ⊢ᶜ⦂ unit ! [ 9 ,+∞⟩
duty-cycle =
  box [ 4 ,+∞⟩ (const reading 42)    -- ∷ [ [ 4 ,+∞⟩ ] Reading
    (perform read ⋆                  -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (perform write here            -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ unit
        (delay 2                     -- ⟨ [ 2 ,+∞⟩ ⟩
          (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
            (perform send here (return ⋆))))))

-- the same resource, reached by idling instead

waiting-instead : [] ⊢ᶜ⦂ unit ! [ 9 ,+∞⟩
waiting-instead =
  box [ 4 ,+∞⟩ (const reading 42)    -- ∷ [ [ 4 ,+∞⟩ ] Reading
    (delay 5                         -- ⟨ [ 5 ,+∞⟩ ⟩
      (unbox (Tl-⟨⟩ Hd) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- one tick short of it, the claim is refused: dropping the store from
-- `duty-cycle` leaves three ticks against a resource promised in four

one-tick-short : ¬ (𝟏ᵣ ·ᵣ opTime read ·ᵣ ιᵣ 2 ≾ᵣ [ 4 ,+∞⟩)
one-tick-short = ≰!

-- two resources on different schedules, claimed at the two points of
-- one run where each has come due: the first after a reading and a
-- store, the second after transmitting as well. Two box bindings stand
-- in the context, and the indices tell them apart. Neither premise is
-- an equality: three ticks have passed against a promise of two, and
-- seven against a promise of six.

two-schedules : [] ⊢ᶜ⦂ unit ! [ 11 ,+∞⟩
two-schedules =
  box [ 2 ,+∞⟩ (const reading 1)     -- ∷ [ [ 2 ,+∞⟩ ] Reading
    (box [ 6 ,+∞⟩ (const reading 2)  -- ∷ [ [ 6 ,+∞⟩ ] Reading
      (perform read ⋆                -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
        (perform write here          -- ⟨ [ 2 ,+∞⟩ ⟩ ∷ unit
          (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
            (perform send here       -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ unit
              (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))))))
                     ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                (perform send here (return ⋆))))))))

-- and the later one is out of reach at the earlier point

not-due-yet : ¬ (𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ [ 6 ,+∞⟩)
not-due-yet = ≰!

-- a resource promised in three ticks, claimed on both sides of an
-- `if`: transmitting takes four outright, while taking a reading takes
-- one and has to be followed by three of idling. The two branches reach
-- the same floor, so the conditional needs no coercion at all, and each
-- passes the premise with a tick to spare.

scheduled-choice : [] ∷ bool ⊢ᶜ⦂ unit ! [ 8 ,+∞⟩
scheduled-choice =
  box [ 3 ,+∞⟩ (const reading 42)            -- ∷ [ [ 3 ,+∞⟩ ] Reading
    (if eternal-var boolₑ (Tl-∷ Hd)
      `then perform send (const reading 0)   -- ⟨ [ 4 ,+∞⟩ ⟩ ∷ unit
              (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                (perform send here (return ⋆)))
      `else perform read ⋆           -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
              (delay 3               -- ⟨ [ 3 ,+∞⟩ ⟩
                (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- without the idling the sampling branch would be two ticks short

------------------------------------------------------------------------
-- Effect handling
--
-- The forwarding clause performs the operation again and resumes, so it
-- spends exactly the grade it is typed at. Handling locks its `in` part
-- by the handled computation's grade, as sequencing does.

forwarded : [] ⊢ᶜ⦂ Reading ! [ 1 ,+∞⟩
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (return here)

-- and a clause may reach an eternal binding across the barrier lock, use
-- its continuation, and answer with what it reached

identified : Node ⊢ᶜ⦂ NodeId ! [ 1 ,+∞⟩
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- what no clause can do here is drop its continuation: it is graded at
-- the operation's own time and a `return` guarantees none of it

no-discarding : ¬ (𝟏ₑ ≾ₑ op-grade read ·ₑ 𝟏ₑ)
no-discarding = ≰!

------------------------------------------------------------------------
-- Handler values
--
-- A handler is a value of type `C ⇛ D`, its return clause locked by the
-- handled grade. The type is contravariant in that grade: a handler for
-- computations taking at least `n` ticks handles any computation
-- guaranteed more, and the result is graded by that computation.

-- forward every operation, and on return claim a resource promised in
-- one tick: the handled computation has taken at least that long

claiming : [] ∷ [ [ 1 ,+∞⟩ ] Reading ⊢ᵛ⦂ (unit ! [ 1 ,+∞⟩) ⇛ (Reading ! 𝟏ₑ)
claiming =
  handler                            -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ unit
    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
      (return here))
    forwarding

-- the handler bound once and handling two computations, a reading and
-- an idle tick

handled-twice : [] ∷ [ [ 1 ,+∞⟩ ] Reading ⊢ᶜ⦂ Reading |×| Reading ! [ 2 ,+∞⟩
handled-twice =
  return claiming                    -- ⟨ [ 0 ,+∞⟩ ⟩ ∷ handler
    ⨟ ((handle perform read ⋆ (return ⋆) `with here)
                                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
        ⨟ ((handle delay 1 (return ⋆) `with fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd)))
                                     -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
            ⨟ return ⦉ fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊))

-- the handler at a computation guaranteed three ticks, by subsumption
-- at its type; the result keeps all three

handled-longer : [] ∷ [ [ 1 ,+∞⟩ ] Reading ⊢ᶜ⦂ Reading ! [ 3 ,+∞⟩
handled-longer =
  handle perform read ⋆ (perform write here (return ⋆))
    `with subV claiming ((<:ᵛ-refl _ !ₛ ≤!) ⇛ₛ <:ᶜ-refl _)

-- coercing the computation to the handler's grade instead keeps one

coerced-longer : [] ∷ [ [ 1 ,+∞⟩ ] Reading ⊢ᶜ⦂ Reading ! [ 1 ,+∞⟩
coerced-longer =
  handle coerce ≤! (perform read ⋆ (perform write here (return ⋆)))
    `with claiming

-- a function taking the handler as its argument

handling-a-reading :
  [] ∷ [ [ 1 ,+∞⟩ ] Reading
    ⊢ᵛ⦂ ((unit ! [ 1 ,+∞⟩) ⇛ (Reading ! 𝟏ₑ)) ⇒ Reading ! [ 1 ,+∞⟩
handling-a-reading =
  fun                                -- ∷ handler
    (handle perform read ⋆ (return ⋆) `with here)

handled-by-argument : [] ∷ [ [ 1 ,+∞⟩ ] Reading ⊢ᶜ⦂ Reading ! [ 1 ,+∞⟩
handled-by-argument = handling-a-reading · claiming

------------------------------------------------------------------------
-- The greatest grade
--
-- Here it is the unit: "at least 0 ticks" claims nothing, so every
-- grade weakens to it and a lock at `⊤ᵣ` lets everything through:
-- nothing ever expires under a lower bound.

everything-weakens : (ε : E) → ε ≾ₑ ⊤ₑ
everything-weakens = ≾-⊤ₑ

reading-survives-⊤ : ⊤ᵣ ≾ᵣ 𝟏ᵣ
reading-survives-⊤ = ≤!

-- so a handler clause may close over a reading: `var`'s bound holds at
-- the barrier and at whatever the clause spends past it

reading-crosses-the-barrier :
  (op : Op) → (ε'' : E) → 𝟏ᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ 𝟏ᵣ
reading-crosses-the-barrier op ε'' = nothing-goes-stale _

-- the node's reading, answered from inside a clause that performs the
-- operation again and resumes first

reported : Node ⊢ᶜ⦂ Reading ! [ 1 ,+∞⟩
reported =
  handle perform read ⋆ (return here)
    `with reporting reading-crosses-the-barrier
    `in                              -- ⟨ [ 1 ,+∞⟩ ⟩ ∷ Reading
      (return here)
