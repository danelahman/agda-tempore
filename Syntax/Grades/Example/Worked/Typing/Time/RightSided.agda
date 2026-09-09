------------------------------------------------------------------------
-- Typed example computations at the grade of upper bounds.            --
--                                                                     --
-- Effect grades and resource grades are both `[0, n ]`, "at most `n`   --
-- time steps", and the operations are graded by the time they may take --
-- at worst: read 1, write 3, send 6.                                   --
--                                                                     --
-- Read as an effect grade, `[0, n ]` is a deadline a computation meets, --
-- and `coerce` may relax it. Read as a resource grade it says at most  --
-- `n` have passed, so `unbox`'s premise `ρ' ≾ᵣ ρ` -- what elapsed is   --
-- within what the box allows -- makes `[ ρ ] A` a lease on a resource: --
-- it is claimable at once and stays claimable while the computation    --
-- spends no more than `ρ`. A claim made too late is refused; there is  --
-- no claim made too early, an upper bound recording no release time.   --
--                                                                     --
-- The two consequences that were the other way round at the lower      --
-- bounds, both checked below:                                          --
--                                                                     --
--   * `var`'s bound `ρ ≾ᵣ uᵣ` holds only at the unit, so a reading     --
--     goes stale as soon as anything at all has been done, and a       --
--     resource that is to survive has to be leased.                    --
--                                                                     --
--   * a handler clause may drop its continuation: the clause's grade   --
--     is a deadline, and returning at once meets every deadline.       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Time.RightSided where

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Time.RightSided
  using (𝕀ᵣ; [0,_]; right-sided-intervals)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send)

open import Syntax.Grades.Example.Worked.Time using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, graded by the time they may take at worst

opTime : Op → 𝕀ᵣ
opTime read  = [0, 1 ]
opTime write = [0, 3 ]
opTime send  = [0, 6 ]

open import Syntax.Grades.Example.Worked.Typing.Core right-sided-intervals opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- The grade of a computation adds up the deadlines of the operations
-- along it, so it is the time the whole run may take at worst.

-- take a reading and hand it back

sampling : [] ⊢C⦂ Reading ‼ [0, 1 ]
sampling = perform read ⋆ (return here)

-- take a reading and store it

storing : [] ⊢C⦂ Unit ‼ [0, 4 ]
storing = perform read ⋆ (perform write here (return ⋆))

-- take a reading and transmit it at once: the reading is the most
-- recent binding where it is used, so `var` asks for nothing

relaying : [] ⊢C⦂ Unit ‼ [0, 7 ]
relaying = perform read ⋆ (perform send here (return ⋆))

-- take a reading, tag it with the node's identifier, and transmit the
-- reading back out of the pair

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ [0, 7 ]
tagged-relaying =
  perform read ⋆
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `var` asks for `ρ ≾ᵣ uᵣ` at a non-eternal type, and the only grade
-- below `[0, 0 ]` is `[0, 0 ]` itself. So a reading is usable only where
-- nothing has been allowed to happen since it was taken: neither
-- `idle-then-transmit` nor `carried-reading` of the lower bounds can be
-- written here.

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling = ≰!

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = ≰!

-- the identifier is eternal, so it is not subject to any of this

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ [0, 1 ]
carried-id =
  perform read ⋆ (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves a computation up the order, and up means "allows
-- more". A deadline may always be relaxed and never tightened.

relaxing-a-deadline : [] ⊢C⦂ Unit ‼ [0, 6 ]
relaxing-a-deadline = coerce ≤! (perform read ⋆ (perform write here (return ⋆)))

tightening-a-deadline : ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ [0, 3 ])
tightening-a-deadline = ≰!

------------------------------------------------------------------------
-- Conditional branching
--
-- Both branches are coerced to one grade, and here that grade is the
-- *larger* deadline: a conditional may take as long as its slower
-- branch.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ [0, 6 ]
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce ≤! (perform send  here (return ⋆))
    `else coerce ≤! (perform write here (return ⋆))

-- the storing branch's own grade will not do for the conditional, the
-- transmitting branch overrunning it

transmitting-takes-longer : ¬ (opTime send ·ₑ uₑ ≾ₑ [0, 3 ])
transmitting-takes-longer = ≰!

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

either-reading : [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ [0, 6 ]
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

sampling-then-branching : [] ⊢C⦂ Unit ‼ [0, 7 ]
sampling-then-branching =
  perform read ⋆
    (if true
      `then coerce ≤! (perform send  here (return ⋆))
      `else coerce ≤! (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a lease that expires
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`, which here reads
-- `elapsed ≤ ρ`: the box may be claimed while what the computation has
-- spent is still within what the box allows. The resource below is
-- leased for six ticks' worth of work.

-- claimed at once, nothing having been spent

claiming-now : [] ⊢C⦂ Unit ‼ [0, 6 ]
claiming-now =
  box {ρ = [0, 6 ]} (const 42)
    (unbox Hd ≤! (perform send here (return ⋆)))

-- claimed after idling two ticks of the six

claim-after-idling : [] ⊢C⦂ Unit ‼ [0, 8 ]
claim-after-idling =
  box {ρ = [0, 6 ]} (const 42)
    (delay 2
      (unbox (Tl-⟨⟩ Hd) ≤!
        (perform send here (return ⋆))))

-- and after taking a reading, which spends one

claim-after-sampling : [] ⊢C⦂ Unit ‼ [0, 7 ]
claim-after-sampling =
  box {ρ = [0, 6 ]} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
        (perform send here (return ⋆))))

-- a transmission and a reading spend seven, which the lease does not
-- cover, so the claim is refused

lease-expired : ¬ (uᵣ ·ᵣ opTime send ·ᵣ opTime read ≾ᵣ [0, 6 ])
lease-expired = ≰!

-- idling spends the lease just as working does

idling-spends-it : ¬ (uᵣ ·ᵣ of-natʳ 7 ≾ᵣ [0, 6 ])
idling-spends-it = ≰!

-- handing a leased resource to a function, which claims it itself

handed-over : [] ⊢C⦂ Unit ‼ [0, 7 ]
handed-over =
  box {ρ = [0, 6 ]} (const 42)
    (lam (perform read ⋆
           (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
             (perform send here (return ⋆))))
      · here)

-- claiming the resource and then choosing what to transmit -- the
-- claimed reading or one taken along the way -- with both branches
-- making the same run

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ [0, 7 ]
either-way =
  box {ρ = [0, 6 ]} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- Each branch discharges the premise at what it has itself spent, so a
-- lease can be open in the cheaper branch and run out in the costlier
-- one. Against a lease of four, the sampling branch still holds it and
-- the transmitting branch has spent it.

open-after-a-reading : uᵣ ·ᵣ opTime read ≾ᵣ [0, 4 ]
open-after-a-reading = ≤!

spent-by-a-transmission : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ [0, 4 ])
spent-by-a-transmission = ≰!

-- leased for six instead, both branches hold it, and the conditional is
-- graded at the deadline of the two

claimed-in-both-branches : [] ⊢C⦂ Unit ‼ [0, 12 ]
claimed-in-both-branches =
  box {ρ = [0, 6 ]} (const 42)
    (if true
      `then coerce ≤!
              (perform read ⋆
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                  (perform send here (return ⋆))))
      `else coerce ≤!
              (perform send (const 0)
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                  (perform send here (return ⋆)))))

------------------------------------------------------------------------
-- Programs written at these intervals
--
-- What a reading cannot do here, a lease can: the run below takes a
-- reading, idles, and transmits a leased resource, the reading it took
-- itself having gone stale in between.

carrying-a-lease : [] ⊢C⦂ Unit ‼ [0, 9 ]
carrying-a-lease =
  box {ρ = [0, 6 ]} (const 42)
    (perform read ⋆
      (delay 2
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤!
          (perform send here (return ⋆)))))

-- the reading taken along the way is not available at that same point

reading-is-not : ¬ (uᵣ ·ᵣ opTime read ·ᵣ of-natʳ 2 ≾ᵣ uᵣ)
reading-is-not = ≰!

-- a lease long enough to cover a transmission as well, spent down to
-- seven of its nine by the time the claim is made

longer-lease : [] ⊢C⦂ Unit ‼ [0, 13 ]
longer-lease =
  box {ρ = [0, 9 ]} (const 42)
    (perform read ⋆
      (perform send (const 0)
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) ≤!
          (perform send here (return ⋆)))))

-- two leases taken out together and claimed at the same point: after a
-- reading and a transmission the longer one is open and the shorter one
-- has run out

long-lease-open : uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ [0, 9 ]
long-lease-open = ≤!

short-lease-run-out : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ [0, 6 ])
short-lease-run-out = ≰!

-- a lease of six spent either way: one branch idles two ticks and then
-- claims it, the other takes a reading and then claims it. Both claim
-- while the lease is still open and transmit afterwards, and the
-- cheaper branch is coerced to the deadline of the other.

spend-it-either-way : [] ∷ Bool ⊢C⦂ Unit ‼ [0, 8 ]
spend-it-either-way =
  box {ρ = [0, 6 ]} (const 42)
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then delay 2
              (unbox (Tl-⟨⟩ Hd) ≤!
                (perform send here (return ⋆)))
      `else coerce ≤!
              (perform read ⋆
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤!
                  (perform send here (return ⋆)))))

-- the claim has to be made before the transmission and not after it:
-- the sampling branch spends one of the six, and transmitting first
-- would spend seven -- `short-lease-run-out` above

claim-before-transmitting : uᵣ ·ᵣ opTime read ≾ᵣ [0, 6 ]
claim-before-transmitting = ≤!

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ [0, 1 ]
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in (return here)

identified : Node ⊢C⦂ NodeId ‼ [0, 1 ]
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- a clause may drop its continuation here: it is graded at a deadline
-- the operation and the resumption would have to meet, and returning at
-- once meets it

nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits read  [0, n ] = z≤n
nothing-fits write [0, n ] = z≤n
nothing-fits send  [0, n ] = z≤n

-- the operations are suppressed, and the grade the handled computation
-- is typed at is unchanged by that

suppressed : [] ⊢C⦂ Unit ‼ [0, 4 ]
suppressed =
  handle perform read ⋆ (perform write here (return ⋆))
    `with discarding {[]} nothing-fits
    `in (return ⋆)
