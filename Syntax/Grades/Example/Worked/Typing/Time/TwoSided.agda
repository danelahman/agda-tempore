------------------------------------------------------------------------
-- Typed example computations at the grade of two-sided windows.       --
--                                                                     --
-- Effect grades and resource grades are both `[ min , max ]`, and the  --
-- operations are graded by the window their execution time falls in:   --
-- read 1, write 2-3, send 4-6.                                         --
--                                                                     --
-- `ρ' ≾ᵣ ρ` asks for both bounds at once -- `min ρ ≤ min ρ'` and       --
-- `max ρ' ≤ max ρ` -- so `unbox`'s premise says what elapsed is late   --
-- enough for the box and still within it. A box is a resource with a   --
-- window: available from `min ρ`, gone after `max ρ`. Both failure     --
-- modes are live here, and the examples below exhibit each: a claim    --
-- made before the window opens and one made after it has closed.       --
--                                                                     --
-- The two endpoints also settle the two questions the one-sided grades --
-- answered one apiece:                                                 --
--                                                                     --
--   * `var`'s bound `ρ ≾ᵣ uᵣ` forces `max ρ` to `0`, so a reading goes --
--     stale as soon as anything has happened -- the upper endpoint     --
--     deciding it, as at the upper bounds.                            --
--                                                                     --
--   * a handler clause cannot drop its continuation, `uₑ ≾ₑ ε` forcing --
--     `min ε` to `0` -- the lower endpoint deciding it, as at the      --
--     lower bounds.                                                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Time.TwoSided where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Time.TwoSided
  using (Interval; [_,_,_]; two-sided-intervals)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send)

open import Syntax.Grades.Example.Worked.Time using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, graded by the window their execution time falls in

opTime : Op → Interval
opTime read  = [ 1 , 1 , ≤! ]
opTime write = [ 2 , 3 , ≤! ]
opTime send  = [ 4 , 6 , ≤! ]

open import Syntax.Grades.Example.Worked.Typing.Core two-sided-intervals opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- Sequencing adds both endpoints, so the grade of a run is the window
-- its total time falls in.

sampling : [] ⊢C⦂ Reading ‼ [ 1 , 1 , ≤! ]
sampling = perform read ⋆ (return here)

storing : [] ⊢C⦂ Unit ‼ [ 3 , 4 , ≤! ]
storing = perform read ⋆ (perform write here (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
relaying = perform read ⋆ (perform send here (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
tagged-relaying =
  perform read ⋆
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ uᵣ` is `0 ≤ min ρ × max ρ ≤ 0`: the upper endpoint has to be
-- `0`, so a reading is usable only where nothing may have happened
-- since it was taken.

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation (_ , hi) = ≰! hi

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling (_ , hi) = ≰! hi

-- the identifier is eternal, and so is not subject to any of this

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ [ 1 , 1 , ≤! ]
carried-id =
  perform read ⋆ (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` widens the window: it may forget the floor downwards and the
-- deadline upwards, and neither the other way.

widening : [] ⊢C⦂ Unit ‼ [ 2 , 6 , ≤! ]
widening =
  coerce (≤! , ≤!) (perform read ⋆ (perform write here (return ⋆)))

raising-the-floor : ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ [ 4 , 6 , ≤! ])
raising-the-floor (lo , _) = ≰! lo

tightening-the-deadline : ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ [ 3 , 3 , ≤! ])
tightening-the-deadline (_ , hi) = ≰! hi

------------------------------------------------------------------------
-- Conditional branching
--
-- The grade both branches are coerced to has to contain both windows,
-- so it is their hull: the floor of the faster branch and the deadline
-- of the slower.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ [ 2 , 6 , ≤! ]
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce (≤! , ≤!) (perform send  here (return ⋆))
    `else coerce (≤! , ≤!) (perform write here (return ⋆))

-- neither branch's own window will do for the conditional

storing-window-too-narrow : ¬ (opTime send ·ₑ uₑ ≾ₑ [ 2 , 3 , ≤! ])
storing-window-too-narrow (_ , hi) = ≰! hi

transmitting-window-too-late : ¬ (opTime write ·ₑ uₑ ≾ₑ [ 4 , 6 , ≤! ])
transmitting-window-too-late (lo , _) = ≰! lo

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

either-reading : [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ [ 4 , 6 , ≤! ]
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var (≤! , ≤!) (Tl-∷ Hd)) (return ⋆)

sampling-then-branching : [] ⊢C⦂ Unit ‼ [ 3 , 7 , ≤! ]
sampling-then-branching =
  perform read ⋆
    (if true
      `then coerce (≤! , ≤!) (perform send  here (return ⋆))
      `else coerce (≤! , ≤!) (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a resource with a window
--
-- A box graded `[ 2 , 6 ]` is available from two ticks and gone after
-- six. Idling two ticks lands in the window; claiming it at once is too
-- early; a reading and a transmission spend up to seven, which is too
-- late.

claim-in-the-window : [] ⊢C⦂ Unit ‼ [ 6 , 8 , ≤! ]
claim-in-the-window =
  box {ρ = [ 2 , 6 , ≤! ]} (const 42)
    (delay 2
      (unbox (Tl-⟨⟩ Hd) (≤! , ≤!)
        (perform send here (return ⋆))))

claim-too-early : ¬ (uᵣ ≾ᵣ [ 2 , 6 , ≤! ])
claim-too-early (lo , _) = ≰! lo

claim-after-a-reading-too-early : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ [ 2 , 6 , ≤! ])
claim-after-a-reading-too-early (lo , _) = ≰! lo

claim-too-late : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ [ 2 , 6 , ≤! ])
claim-too-late (_ , hi) = ≰! hi

-- a window that opens at one tick is within reach of a single reading

claim-after-sampling : [] ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
claim-after-sampling =
  box {ρ = [ 1 , 6 , ≤! ]} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
        (perform send here (return ⋆))))

handed-over : [] ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
handed-over =
  box {ρ = [ 1 , 6 , ≤! ]} (const 42)
    (lam (perform read ⋆
           (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
             (perform send here (return ⋆))))
      · here)

-- and one claimable at once is one whose window is open from the start

claiming-now : [] ⊢C⦂ Unit ‼ [ 4 , 6 , ≤! ]
claiming-now =
  box {ρ = [ 0 , 6 , ≤! ]} (const 42)
    (unbox Hd (≤! , ≤!) (perform send here (return ⋆)))

-- claiming the resource and then choosing what to transmit, with both
-- branches making the same run

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
either-way =
  box {ρ = [ 1 , 6 , ≤! ]} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var (≤! , ≤!) (Tl-∷ Hd)) (return ⋆))))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- Against the window `[ 1 , 6 ]`, a reading is inside it and so is a
-- transmission, so both branches may claim the resource.

claimed-in-both-branches : [] ⊢C⦂ Unit ‼ [ 5 , 12 , ≤! ]
claimed-in-both-branches =
  box {ρ = [ 1 , 6 , ≤! ]} (const 42)
    (if true
      `then coerce (≤! , ≤!)
              (perform read ⋆
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                  (perform send here (return ⋆))))
      `else coerce (≤! , ≤!)
              (perform send (const 0)
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                  (perform send here (return ⋆)))))

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing types its continuation under the lock `⟨ mapᵉ ε ⟩`, where
-- `ε` is the grade the first part is *typed at*, so a `coerce` on that
-- first part changes what the continuation may claim -- and here the
-- coercion moves both endpoints, so it can close a box from either
-- side. Below it is the floor that gives way: widening the prefix's
-- window lowers what it guarantees, and the box is no longer late
-- enough to be claimed.

-- a reading and a store take between three and four ticks, which lands
-- inside the box's window

claim-after-a-store : [] ⊢C⦂ Unit ‼ [ 7 , 10 , ≤! ]
claim-after-a-store =
  box {ρ = [ 3 , 6 , ≤! ]} (const 42)
    ((perform read ⋆ (perform write here (return ⋆)))
      ⨟ unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
          (perform send here (return ⋆)))

-- widening that to `[ 2 , 6 ]` first drops its floor to two, and the
-- box asks for three

coercing-closes-it : ¬ (uᵣ ·ᵣ [ 2 , 6 , ≤! ] ≾ᵣ [ 3 , 6 , ≤! ])
coercing-closes-it (lo , _) = ≰! lo

-- the same program with the coercion, against a box whose window opens
-- where the coerced grade does

claim-after-a-coerced-store : [] ⊢C⦂ Unit ‼ [ 6 , 12 , ≤! ]
claim-after-a-coerced-store =
  box {ρ = [ 2 , 6 , ≤! ]} (const 42)
    (coerce {ε' = [ 2 , 6 , ≤! ]} (≤! , ≤!)
       (perform read ⋆ (perform write here (return ⋆)))
      ⨟ unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
          (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Programs written at these windows
--
-- Both ends of a window in one `if`: the branch that idles two ticks
-- opens it, the branch that transmits lands on its far edge, and the
-- conditional is graded at the hull of the two.

window-in-a-branch : [] ∷ Bool ⊢C⦂ Unit ‼ [ 6 , 12 , ≤! ]
window-in-a-branch =
  box {ρ = [ 2 , 6 , ≤! ]} (const 42)
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce (≤! , ≤!)
              (delay 2
                (unbox (Tl-⟨⟩ Hd) (≤! , ≤!)
                  (perform send here (return ⋆))))
      `else coerce (≤! , ≤!)
              (perform send (const 0)
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                  (perform send here (return ⋆)))))

-- one reading more in the transmitting branch and the window has closed

one-reading-too-many : ¬ (uᵣ ·ᵣ opTime send ·ᵣ opTime read ≾ᵣ [ 2 , 6 , ≤! ])
one-reading-too-many (_ , hi) = ≰! hi

-- Two staggered resources, each claimed at the one point of the run
-- where its own window is open: the first after idling two ticks, the
-- second after transmitting the first as well.

staggered : [] ⊢C⦂ Unit ‼ [ 10 , 14 , ≤! ]
staggered =
  box {ρ = [ 2 , 6 , ≤! ]} (const 1)
    (box {ρ = [ 6 , 12 , ≤! ]} (const 2)
      (delay 2
        (unbox (Tl-⟨⟩ (Tl-∷ Hd)) (≤! , ≤!)
          (perform send here
            (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ≤!)
              (perform send here (return ⋆)))))))

-- the points cannot be swapped: at the earlier one the second window
-- has not opened, and at the later one the first has closed

second-not-open-yet : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ [ 6 , 12 , ≤! ])
second-not-open-yet (lo , _) = ≰! lo

first-closed-by-then : ¬ (uᵣ ·ᵣ of-natʳ 2 ·ᵣ opTime send ≾ᵣ [ 2 , 6 , ≤! ])
first-closed-by-then (_ , hi) = ≰! hi

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ [ 1 , 1 , ≤! ]
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in (return here)

identified : Node ⊢C⦂ NodeId ‼ [ 1 , 1 , ≤! ]
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- and no clause may drop its continuation: `uₑ ≾ₑ op-grade op ·ₑ ε''`
-- asks the clause's floor to be `0`, and an operation's is not

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding (lo , _) = ≰! lo
