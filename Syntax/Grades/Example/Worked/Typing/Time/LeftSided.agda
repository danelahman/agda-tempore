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
-- The grade of a computation is the sum of the grades of the operations
-- along it, so it is the time the whole run is guaranteed to take.

-- take a reading and hand it back

sampling : [] ⊢C⦂ Reading ‼ [ 1 ,+∞⟩
sampling = perform read ⋆ (return here)

-- take a reading and store it

storing : [] ⊢C⦂ Unit ‼ [ 3 ,+∞⟩
storing = perform read ⋆ (perform write here (return ⋆))

-- take a reading and transmit it

relaying : [] ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
relaying = perform read ⋆ (perform send here (return ⋆))

-- take a reading, tag it with the node's identifier, and transmit the
-- reading back out of the pair; pairing costs no time, so the grade is
-- the one `relaying` has

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
tagged-relaying =
  perform read ⋆
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
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
-- the idling: `≤!` here is `var`'s bound at the two ticks that passed

idle-then-transmit : [] ⊢C⦂ Unit ‼ [ 7 ,+∞⟩
idle-then-transmit =
  perform read ⋆
    (delay 2
      (perform send (fresh-var ≤! (Tl-⟨⟩ Hd))
        (return ⋆)))

-- the identifier crosses the reading's execution time because it is
-- eternal, and asks for no bound at all

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ [ 1 ,+∞⟩
carried-id =
  perform read ⋆ (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

-- a reading crosses it because nothing goes stale

carried-reading : [] ∷ Reading ⊢C⦂ Reading ‼ [ 1 ,+∞⟩
carried-reading =
  perform read ⋆ (return (fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves a computation up the order, and up means "guarantees
-- less". A guarantee may always be forgotten and never invented.

forgetting-time : [] ⊢C⦂ Unit ‼ [ 2 ,+∞⟩
forgetting-time = coerce ≤! (perform read ⋆ (perform write here (return ⋆)))

inventing-time : ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ [ 4 ,+∞⟩)
inventing-time = ≰!

------------------------------------------------------------------------
-- Conditional branching
--
-- The two branches are typed at one grade, so both are coerced to it.
-- Here that grade is the *smaller* floor: a conditional guarantees only
-- what its faster branch does.

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

-- branching on data that an operation produced

sampling-then-branching : [] ⊢C⦂ Unit ‼ [ 3 ,+∞⟩
sampling-then-branching =
  perform read ⋆
    (if true
      `then coerce ≤! (perform send  here (return ⋆))
      `else coerce ≤! (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a resource that becomes available
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`, which here reads `ρ ≤ elapsed`:
-- the box may be claimed once at least as much time has passed as it
-- asks for. The boxed value is a constant, which is what "available in
-- `Γ ⟨ ρ ⟩`" comes to for data the environment supplies.

-- a reading promised in two ticks, claimed after idling exactly that
-- long, and transmitted

claim-after-idling : [] ⊢C⦂ Unit ‼ [ 6 ,+∞⟩
claim-after-idling =
  box {ρ = [ 2 ,+∞⟩} (const 42)
    (delay 2
      (unbox (Tl-⟨⟩ Hd) ≤!
        (perform send here (return ⋆))))

-- taking a reading is one tick's worth of waiting, which is not enough
-- for that box

claim-after-sampling-fails : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ [ 2 ,+∞⟩)
claim-after-sampling-fails = ≰!

-- and claiming it at once is not enough either

claim-at-once-fails : ¬ (uᵣ ≾ᵣ [ 2 ,+∞⟩)
claim-at-once-fails = ≰!

-- a resource promised in one tick is claimable after a reading, since
-- performing an operation is how time passes

claim-after-sampling : [] ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
claim-after-sampling =
  box {ρ = [ 1 ,+∞⟩} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
        (perform send here (return ⋆))))

-- a resource claimable with nothing elapsed is one that promises
-- nothing: `uᵣ ≾ᵣ ρ` forces the box's grade to the unit

claiming-now : [] ⊢C⦂ Unit ‼ [ 4 ,+∞⟩
claiming-now =
  box {ρ = [ 0 ,+∞⟩} (const 42)
    (unbox Hd ≤! (perform send here (return ⋆)))

-- a boxed resource crosses a binder as an ordinary value: the function
-- takes the box and makes the claim itself

handed-over : [] ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
handed-over =
  box {ρ = [ 1 ,+∞⟩} (const 42)
    (lam (perform read ⋆
           (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
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

-- promised in one tick instead, both branches reach it, and the
-- conditional is graded at the floor of the two

claimed-in-both-branches : [] ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
claimed-in-both-branches =
  box {ρ = [ 1 ,+∞⟩} (const 42)
    (if true
      `then coerce ≤!
              (perform read ⋆
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                  (perform send here (return ⋆))))
      `else coerce ≤!
              (perform send (const 0)
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                  (perform send here (return ⋆)))))

-- claiming the resource and then choosing what to transmit -- the
-- claimed reading or one taken along the way -- with both branches
-- making the same run

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ [ 5 ,+∞⟩
either-way =
  box {ρ = [ 1 ,+∞⟩} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

------------------------------------------------------------------------
-- Programs written at these intervals
--
-- A lower bound counts time and nothing else, so what a run does
-- between boxing a resource and claiming it does not matter -- only how
-- long it takes. The two runs below reach the same resource, one by
-- working and one by waiting, and are graded alike.

-- a resource promised in five ticks, reached by working: a reading and
-- a store are three ticks, and two of idling make five

duty-cycle : [] ⊢C⦂ Unit ‼ [ 9 ,+∞⟩
duty-cycle =
  box {ρ = [ 5 ,+∞⟩} (const 42)
    (perform read ⋆
      (perform write here
        (delay 2
          (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))) ≤!
            (perform send here (return ⋆))))))

-- the same resource, reached by idling instead

waiting-instead : [] ⊢C⦂ Unit ‼ [ 9 ,+∞⟩
waiting-instead =
  box {ρ = [ 5 ,+∞⟩} (const 42)
    (delay 5
      (unbox (Tl-⟨⟩ Hd) ≤!
        (perform send here (return ⋆))))

-- one tick short of it, the claim is refused: dropping the store from
-- `duty-cycle` leaves four ticks against a resource promised in five

one-tick-short : ¬ (uᵣ ·ᵣ opTime read ·ᵣ of-natʳ 2 ≾ᵣ [ 5 ,+∞⟩)
one-tick-short = ≰!

-- two resources on different schedules, claimed at the two points of
-- one run where each has come due: the first after a reading, the
-- second after transmitting as well

two-schedules : [] ⊢C⦂ Unit ‼ [ 9 ,+∞⟩
two-schedules =
  box {ρ = [ 1 ,+∞⟩} (const 1)
    (box {ρ = [ 5 ,+∞⟩} (const 2)
      (perform read ⋆
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) ≤!
          (perform send here
            (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))))) ≤!
              (perform send here (return ⋆)))))))

-- and the later one is out of reach at the earlier point

not-due-yet : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ [ 5 ,+∞⟩)
not-due-yet = ≰!

-- a resource promised in four ticks, claimed on both sides of an `if`:
-- transmitting takes the four outright, while taking a reading takes
-- one and has to be followed by three of idling. The two branches reach
-- the same floor, so the conditional needs no coercion at all.

scheduled-choice : [] ∷ Bool ⊢C⦂ Unit ‼ [ 8 ,+∞⟩
scheduled-choice =
  box {ρ = [ 4 ,+∞⟩} (const 42)
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then perform send (const 0)
              (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                (perform send here (return ⋆)))
      `else perform read ⋆
              (delay 3
                (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤!
                  (perform send here (return ⋆)))))

-- without the idling the sampling branch would be three ticks short:
-- `unreachable-after-a-reading` above is what it would need

------------------------------------------------------------------------
-- Effect handling
--
-- The forwarding clause performs the operation again and resumes, so it
-- spends exactly the grade it is typed at.

forwarded : [] ⊢C⦂ Reading ‼ [ 1 ,+∞⟩
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in (return here)

-- and a clause may close over the eternal part of the context, use its
-- continuation, and answer with what it closed over

identified : Node ⊢C⦂ NodeId ‼ [ 1 ,+∞⟩
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- what no clause can do here is drop its continuation: it is graded at
-- the operation's own time and a `return` guarantees none of it

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = ≰!
