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
--                                                                     --
-- The comments inside the programs say what each former appends to the --
-- context its subcomputation is typed in: `⟨ ρ ⟩` a lock, `∷ A` a      --
-- binding. They write an interval as `[ min , max ]`, without the      --
-- `min ≤ max` proof the constructor also carries.                      --
--                                                                     --
-- The upper endpoint ranges over the extended naturals, so every       --
-- window written below is `[ min , ↑ max ]`; `[ 0 , ∞ ]` is the        --
-- greatest grade, bounding the elapsed time at neither end.            --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Time.TwoSided where

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Product using (_,_)

open import Util.Equality

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; ↑_; ∞; two-sided-intervals-with-∞)
  renaming ([_,_,_] to ⌈_,_,_⌉)

-- every window written below has a finite upper endpoint; `⌈ 0 , ∞ , _ ⌉`
-- is the greatest grade, bounding the elapsed time at neither end

[_,_,_] : (m n : ℕ) → m ≤ n → Interval∞
[ m , n , p ] = ⌈ m , ↑ n , p ⌉

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send)

open import Syntax.Grades.Example.Worked.Time using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, graded by the window their execution time falls in

opTime : Op → Interval∞
opTime read  = [ 1 , 1 , ≤! ]
opTime write = [ 2 , 3 , ≤! ]
opTime send  = [ 4 , 6 , ≤! ]

open import Syntax.Grades.Example.Worked.Typing.Core
  two-sided-intervals-with-∞ opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- Sequencing adds both endpoints, so the grade of a run is the window
-- its total time falls in, and each `perform` locks the context by the
-- window its own operation takes.

sampling : [] ⊢C⦂ Reading ‼ [ 1 , 1 , ≤! ]
sampling =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ [ 3 , 4 , ≤! ]
storing =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (perform write here              -- ⟨ [ 2 , 3 ] ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
relaying =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (perform send here               -- ⟨ [ 4 , 6 ] ⟩ ∷ Unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
tagged-relaying =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ uᵣ` is `0 ≤ min ρ × max ρ ≤ 0`: the upper endpoint has to be
-- `0`, so a reading is usable only where no lock stands between its
-- binding and its use.

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation (_ , hi) = ≰! hi

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling (_ , hi) = ≰! hi

-- the identifier is eternal, and so is not subject to any of this

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ [ 1 , 1 , ≤! ]
carried-id =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` widens the window: it may forget the floor downwards and the
-- deadline upwards, and neither the other way. The context is untouched.

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
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (if true
      `then coerce (≤! , ≤!) (perform send  here (return ⋆))
      `else coerce (≤! , ≤!) (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a resource with a window
--
-- A box graded `[ 2 , 6 ]` is available from two ticks and gone after
-- six, and what it is compared against is the product of the locks
-- between its binding and the claim. Idling three ticks lands inside
-- the window, clear of both endpoints; claiming it at once is too
-- early; a reading and a transmission spend up to seven, too late.

claim-in-the-window : [] ⊢C⦂ Unit ‼ [ 7 , 9 , ≤! ]
claim-in-the-window =
  box {ρ = [ 2 , 6 , ≤! ]} (const 42)
                                     -- ∷ [ [ 2 , 6 ] ] Reading
    (delay 3                         -- ⟨ [ 3 , 3 ] ⟩
      (unbox (Tl-⟨⟩ Hd) (≤! , ≤!)    -- ∷ Reading
        (perform send here (return ⋆))))

claim-too-early : ¬ (uᵣ ≾ᵣ [ 2 , 6 , ≤! ])
claim-too-early (lo , _) = ≰! lo

claim-after-a-reading-too-early : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ [ 2 , 6 , ≤! ])
claim-after-a-reading-too-early (lo , _) = ≰! lo

claim-too-late : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ [ 2 , 6 , ≤! ])
claim-too-late (_ , hi) = ≰! hi

-- a window that opens at one tick is within reach of a reading and a
-- store, which take between three and four: past the floor and inside
-- the deadline, with neither endpoint met exactly

claim-after-storing : [] ⊢C⦂ Unit ‼ [ 7 , 10 , ≤! ]
claim-after-storing =
  box {ρ = [ 1 , 6 , ≤! ]} (const 42)
                                     -- ∷ [ [ 1 , 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (perform write here            -- ⟨ [ 2 , 3 ] ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ≤!)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

handed-over : [] ⊢C⦂ Unit ‼ [ 6 , 9 , ≤! ]
handed-over =
  box {ρ = [ 1 , 6 , ≤! ]} (const 42)
                                     -- ∷ [ [ 1 , 6 ] ] Reading
    (lam                             -- ∷ [ [ 1 , 6 ] ] Reading
       (perform write (const 0)      -- ⟨ [ 2 , 3 ] ⟩ ∷ Unit
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

-- and one claimable at once is one whose window is open from the start

claiming-now : [] ⊢C⦂ Unit ‼ [ 4 , 6 , ≤! ]
claiming-now =
  box {ρ = [ 0 , 6 , ≤! ]} (const 42)
                                     -- ∷ [ [ 0 , 6 ] ] Reading
    (unbox Hd (≤! , ≤!)              -- ∷ Reading
      (perform send here (return ⋆)))

-- claiming the resource and then choosing what to transmit, with both
-- branches making the same run

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ [ 5 , 7 , ≤! ]
either-way =
  box {ρ = [ 0 , 6 , ≤! ]} (const 42)
                                     -- ∷ [ [ 0 , 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var (≤! , ≤!) (Tl-∷ Hd)) (return ⋆))))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- Against the window `[ 0 , 8 ]`, a reading is inside it and so is a
-- transmission, so both branches may claim the resource -- and neither
-- meets an endpoint exactly.

claimed-in-both-branches : [] ⊢C⦂ Unit ‼ [ 5 , 12 , ≤! ]
claimed-in-both-branches =
  box {ρ = [ 0 , 8 , ≤! ]} (const 42)
                                     -- ∷ [ [ 0 , 8 ] ] Reading
    (if true
      `then coerce (≤! , ≤!)
              (perform read ⋆        -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce (≤! , ≤!)
              (perform send (const 0)
                                     -- ⟨ [ 4 , 6 ] ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing locks its continuation by the grade the first part is
-- *typed at*, so a `coerce` on that part changes the lock -- and here
-- the coercion moves both endpoints, so it can close a box from either
-- side. Below it is the floor that gives way: widening the prefix's
-- window lowers what it guarantees, and the box is no longer late
-- enough to be claimed.

-- a reading and a store take between three and four ticks, which lands
-- inside the box's window

claim-after-a-store : [] ⊢C⦂ Unit ‼ [ 7 , 10 , ≤! ]
claim-after-a-store =
  box {ρ = [ 3 , 6 , ≤! ]} (const 42)
                                     -- ∷ [ [ 3 , 6 ] ] Reading
    ((perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 3 , 4 ] ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
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
                                     -- ∷ [ [ 2 , 6 ] ] Reading
    (coerce {ε' = [ 2 , 6 , ≤! ]} (≤! , ≤!)
       (perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 2 , 6 ] ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Programs written at these windows
--
-- Both ends of a window in one `if`: the branch that idles three ticks
-- claims it clear of both endpoints, the branch that transmits lands on
-- its far edge, and both are coerced to a window containing the two.

window-in-a-branch : [] ∷ Bool ⊢C⦂ Unit ‼ [ 6 , 12 , ≤! ]
window-in-a-branch =
  box {ρ = [ 2 , 6 , ≤! ]} (const 42)
                                     -- ∷ [ [ 2 , 6 ] ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce (≤! , ≤!)
              (delay 3               -- ⟨ [ 3 , 3 ] ⟩
                (unbox (Tl-⟨⟩ Hd) (≤! , ≤!)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce (≤! , ≤!)
              (perform send (const 0)
                                     -- ⟨ [ 4 , 6 ] ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- one reading more in the transmitting branch and the window has closed

one-reading-too-many : ¬ (uᵣ ·ᵣ opTime send ·ᵣ opTime read ≾ᵣ [ 2 , 6 , ≤! ])
one-reading-too-many (_ , hi) = ≰! hi

-- Two staggered resources, each claimed at the one point of the run
-- where its own window is open: the first after idling three ticks, the
-- second after transmitting the first as well. Two box bindings stand
-- in the context, and the indices tell them apart.

staggered : [] ⊢C⦂ Unit ‼ [ 11 , 15 , ≤! ]
staggered =
  box {ρ = [ 2 , 6 , ≤! ]} (const 1) -- ∷ [ [ 2 , 6 ] ] Reading
    (box {ρ = [ 6 , 12 , ≤! ]} (const 2)
                                     -- ∷ [ [ 6 , 12 ] ] Reading
      (delay 3                       -- ⟨ [ 3 , 3 ] ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ Hd)) (≤! , ≤!)
                                     -- ∷ Reading
          (perform send here         -- ⟨ [ 4 , 6 ] ⟩ ∷ Unit
            (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ≤!)
                                     -- ∷ Reading
              (perform send here (return ⋆)))))))

-- the points cannot be swapped: at the earlier one the second window
-- has not opened, and at the later one the first has closed

second-not-open-yet : ¬ (uᵣ ·ᵣ of-natʳ 3 ≾ᵣ [ 6 , 12 , ≤! ])
second-not-open-yet (lo , _) = ≰! lo

first-closed-by-then : ¬ (uᵣ ·ᵣ of-natʳ 3 ·ᵣ opTime send ≾ᵣ [ 2 , 6 , ≤! ])
first-closed-by-then (_ , hi) = ≰! hi

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ [ 1 , 1 , ≤! ]
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ [ 1 , 1 , ≤! ]
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- and no clause may drop its continuation: `uₑ ≾ₑ op-grade op ·ₑ ε''`
-- asks the clause's floor to be `0`, and an operation's is not

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding (lo , _) = ≰! lo

------------------------------------------------------------------------
-- The greatest grade
--
-- `⌈ 0 , ∞ , _ ⌉` bounds the elapsed time at neither end, so every
-- grade weakens to it. It does not absorb: sequencing keeps the lower
-- bound of whatever follows it.

everything-weakens : (ε : E) → ε ≾ₑ ⊤ₑ
everything-weakens = ≾-⊤ₑ

⊤-keeps-the-floor : (⊤ₑ ·ₑ [ 4 , 6 , ≤! ]) ≡ (⌈ 4 , ∞ , _ ⌉)
⊤-keeps-the-floor = refl
