------------------------------------------------------------------------
-- Typed example computations at the grade of two-sided windows.      --
--                                                                    --
-- Effect grades and resource grades are both `[ min , max ]`, and    --
-- the operations are graded by the window in which their execution   --
-- time lies: read 1, write 2-3, send 4-6.                            --
--                                                                    --
-- `ρ' ≾ᵣ ρ` requires both `min ρ ≤ min ρ'` and `max ρ' ≤ max ρ`, so  --
-- the premise of `unbox` states that the elapsed grade is late       --
-- enough for the box and still within it. A box is a resource with a --
-- window: available from `min ρ` and unavailable after `max ρ`. The  --
-- examples below exhibit both failures: a claim made before the      --
-- window opens and one made after it closes.                         --
--                                                                    --
-- The two endpoints settle the two questions that the one-sided      --
-- grades settle one each:                                            --
--                                                                    --
--   * the bound `ρ ≾ᵣ 𝟏ᵣ` of `var` forces `max ρ` to `0`, so a       --
--     reading goes stale after any activity; the upper endpoint      --
--     decides it, as at the upper bounds.                            --
--                                                                    --
--   * a handler clause cannot discard its continuation, `𝟏ₑ ≾ₑ ε`    --
--     forcing `min ε` to `0`; the lower endpoint decides it, as at   --
--     the lower bounds.                                              --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. They write an interval as `[ min , max ]`.        --
--                                                                    --
-- The upper endpoint ranges over the extended naturals, so every     --
-- window below is `[ min , ↑ max ]`; `[ 0 , ∞ ]` is the greatest     --
-- grade, bounding the elapsed time at neither end.                   --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Time.TwoSided where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_,_)

open import Util.Equality

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True)

open import Grades.Examples.Time.TwoSidedWithInfinity
  using (Interval∞; ↑_; ∞; two-sided-intervals-with-∞)
  renaming ([_,_] to ⌈_,_⌉)

-- every window written below has a finite upper endpoint; `⌈ 0 , ∞ ⌉`
-- is the greatest grade, bounding the elapsed time at neither end

[_,_] : (m n : ℕ) {m≤n : True (m ≤? n)} → Interval∞
[ m , n ] {m≤n} = ⌈ m , ↑ n ⌉ {m≤n}

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, graded by the window their execution time falls in

open import Grades.Examples.Worked.Operations.Grading using (module Time-TwoSided)
open Time-TwoSided using (opTime) public

open import MonomorphicCalculus.Examples.Typing.Core
  two-sided-intervals-with-∞ opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- Sequencing adds both endpoints, so the grade of a run is the window
-- its total time falls in, and each `perform` locks the context by the
-- window its own operation takes.

sampling : [] ⊢C⦂ Reading ! [ 1 , 1 ]
sampling =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ unit ! [ 3 , 4 ]
storing =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (perform write here              -- ⟨ [ 2 , 3 ] ⟩ ∷ unit
      (return ⋆))

relaying : [] ⊢C⦂ unit ! [ 5 , 7 ]
relaying =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (perform send here               -- ⟨ [ 4 , 6 ] ⟩ ∷ unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ unit ! [ 5 , 7 ]
tagged-relaying =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `with perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ 𝟏ᵣ` is `0 ≤ min ρ × max ρ ≤ 0`: the upper endpoint has to be
-- `0`, so a reading is usable only where no lock stands between its
-- binding and its use.

reading-stale-after-an-operation : ¬ (𝟏ᵣ ·ᵣ opTime read ≾ᵣ 𝟏ᵣ)
reading-stale-after-an-operation (_ , hi) = ≰! hi

reading-stale-after-idling : ¬ (𝟏ᵣ ·ᵣ ιᵣ 2 ≾ᵣ 𝟏ᵣ)
reading-stale-after-idling (_ , hi) = ≰! hi

-- the identifier is eternal, and so is not subject to any of this

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ! [ 1 , 1 ]
carried-id =
  perform read ⋆                     -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` enlarges the window: it may forget the floor downwards and the
-- deadline upwards, and neither the other way. The context is untouched.

enlarging-the-window : [] ⊢C⦂ unit ! [ 2 , 6 ]
enlarging-the-window =
  coerce (≤! , ≤!) (perform read ⋆ (perform write here (return ⋆)))

raising-the-floor : ¬ (opTime read ·ₑ (opTime write ·ₑ 𝟏ₑ) ≾ₑ [ 4 , 6 ])
raising-the-floor (lo , _) = ≰! lo

tightening-the-deadline : ¬ (opTime read ·ₑ (opTime write ·ₑ 𝟏ₑ) ≾ₑ [ 3 , 3 ])
tightening-the-deadline (_ , hi) = ≰! hi

------------------------------------------------------------------------
-- Conditional branching
--
-- The grade both branches are coerced to has to contain both windows,
-- so it is their hull: the floor of the faster branch and the deadline
-- of the slower.

branching : [] ∷ bool ∷ Reading ⊢C⦂ unit ! [ 2 , 6 ]
branching =
  if eternal-var boolₑ (Tl-∷ Hd)
    `then coerce (≤! , ≤!) (perform send  here (return ⋆))
    `else coerce (≤! , ≤!) (perform write here (return ⋆))

-- neither branch's own window will do for the conditional

storing-window-too-tight : ¬ (opTime send ·ₑ 𝟏ₑ ≾ₑ [ 2 , 3 ])
storing-window-too-tight (_ , hi) = ≰! hi

transmitting-window-too-late : ¬ (opTime write ·ₑ 𝟏ₑ ≾ₑ [ 4 , 6 ])
transmitting-window-too-late (lo , _) = ≰! lo

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

either-reading : [] ∷ bool ∷ Reading ∷ Reading ⊢C⦂ unit ! [ 4 , 6 ]
either-reading =
  if eternal-var boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var (≤! , ≤!) (Tl-∷ Hd)) (return ⋆)

sampling-then-branching : [] ⊢C⦂ unit ! [ 3 , 7 ]
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

claim-in-the-window : [] ⊢C⦂ unit ! [ 7 , 9 ]
claim-in-the-window =
  box [ 2 , 6 ] (const 42)           -- ∷ [ [ 2 , 6 ] ] Reading
    (delay 3                         -- ⟨ [ 3 , 3 ] ⟩
      (unbox (Tl-⟨⟩ Hd) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

claim-too-early : ¬ (𝟏ᵣ ≾ᵣ [ 2 , 6 ])
claim-too-early (lo , _) = ≰! lo

claim-after-a-reading-too-early : ¬ (𝟏ᵣ ·ᵣ opTime read ≾ᵣ [ 2 , 6 ])
claim-after-a-reading-too-early (lo , _) = ≰! lo

claim-too-late : ¬ (𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ [ 2 , 6 ])
claim-too-late (_ , hi) = ≰! hi

-- a window that opens at one tick is within reach of a reading and a
-- store, which take between three and four: past the floor and inside
-- the deadline, with neither endpoint met exactly

claim-after-storing : [] ⊢C⦂ unit ! [ 7 , 10 ]
claim-after-storing =
  box [ 1 , 6 ] (const 42)           -- ∷ [ [ 1 , 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (perform write here            -- ⟨ [ 2 , 3 ] ⟩ ∷ unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

handed-over : [] ⊢C⦂ unit ! [ 6 , 9 ]
handed-over =
  box [ 1 , 6 ] (const 42)           -- ∷ [ [ 1 , 6 ] ] Reading
    (fun                             -- ∷ [ [ 1 , 6 ] ] Reading
       (perform write (const 0)      -- ⟨ [ 2 , 3 ] ⟩ ∷ unit
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

-- and one claimable at once is one whose window is open from the start

claiming-now : [] ⊢C⦂ unit ! [ 4 , 6 ]
claiming-now =
  box [ 0 , 6 ] (const 42)           -- ∷ [ [ 0 , 6 ] ] Reading
    (unbox Hd (≤! , ≤!) (<:ᵛ-refl _) -- ∷ Reading
      (perform send here (return ⋆)))

-- claiming the resource and then choosing what to transmit, with both
-- branches making the same run

either-way : [] ∷ bool ⊢C⦂ unit ! [ 5 , 7 ]
either-way =
  box [ 0 , 6 ] (const 42)           -- ∷ [ [ 0 , 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
        (if eternal-var boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var (≤! , ≤!) (Tl-∷ Hd)) (return ⋆))))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- Against the window `[ 0 , 8 ]`, a reading is inside it and so is a
-- transmission, so both branches may claim the resource, and neither
-- meets an endpoint exactly.

claimed-in-both-branches : [] ⊢C⦂ unit ! [ 5 , 12 ]
claimed-in-both-branches =
  box [ 0 , 8 ] (const 42)           -- ∷ [ [ 0 , 8 ] ] Reading
    (if true
      `then coerce (≤! , ≤!)
              (perform read ⋆        -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce (≤! , ≤!)
              (perform send (const 0)
                                     -- ⟨ [ 4 , 6 ] ⟩ ∷ unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing locks its continuation by the grade the first part is
-- typed at, so a `coerce` there changes the lock, and here it moves
-- both endpoints and can close a box from either side. Below it is the
-- floor that gives way.

-- a reading and a store take between three and four ticks, which lands
-- inside the box's window

claim-after-a-store : [] ⊢C⦂ unit ! [ 7 , 10 ]
claim-after-a-store =
  box [ 3 , 6 ] (const 42)           -- ∷ [ [ 3 , 6 ] ] Reading
    ((perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 3 , 4 ] ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- enlarging that to `[ 2 , 6 ]` first drops its floor to two, and the
-- box asks for three

coercing-closes-it : ¬ (𝟏ᵣ ·ᵣ [ 2 , 6 ] ≾ᵣ [ 3 , 6 ])
coercing-closes-it (lo , _) = ≰! lo

-- the same program with the coercion, against a box whose window opens
-- where the coerced grade does

claim-after-a-coerced-store : [] ⊢C⦂ unit ! [ 6 , 12 ]
claim-after-a-coerced-store =
  box [ 2 , 6 ] (const 42)           -- ∷ [ [ 2 , 6 ] ] Reading
    (coerce {ε' = [ 2 , 6 ]} (≤! , ≤!)
       (perform read ⋆ (perform write here (return ⋆)))
      ⨟                              -- ⟨ [ 2 , 6 ] ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Programs written at these windows
--
-- Both ends of a window in one `if`: the branch that idles three ticks
-- claims it clear of both endpoints, the branch that transmits lands on
-- its far edge, and both are coerced to a window containing the two.

window-in-a-branch : [] ∷ bool ⊢C⦂ unit ! [ 6 , 12 ]
window-in-a-branch =
  box [ 2 , 6 ] (const 42)           -- ∷ [ [ 2 , 6 ] ] Reading
    (if eternal-var boolₑ (Tl-∷ Hd)
      `then coerce (≤! , ≤!)
              (delay 3               -- ⟨ [ 3 , 3 ] ⟩
                (unbox (Tl-⟨⟩ Hd) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce (≤! , ≤!)
              (perform send (const 0)
                                     -- ⟨ [ 4 , 6 ] ⟩ ∷ unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- one reading more in the transmitting branch and the window has closed

one-reading-too-many : ¬ (𝟏ᵣ ·ᵣ opTime send ·ᵣ opTime read ≾ᵣ [ 2 , 6 ])
one-reading-too-many (_ , hi) = ≰! hi

-- Two staggered resources, each claimed at the one point of the run
-- where its own window is open: the first after idling three ticks, the
-- second after transmitting the first as well. Two box bindings stand
-- in the context, and the indices tell them apart.

staggered : [] ⊢C⦂ unit ! [ 11 , 15 ]
staggered =
  box [ 2 , 6 ] (const 1)            -- ∷ [ [ 2 , 6 ] ] Reading
    (box [ 6 , 12 ] (const 2)
                                     -- ∷ [ [ 6 , 12 ] ] Reading
      (delay 3                       -- ⟨ [ 3 , 3 ] ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ Hd)) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here         -- ⟨ [ 4 , 6 ] ⟩ ∷ unit
            (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
              (perform send here (return ⋆)))))))

-- the points cannot be swapped: at the earlier one the second window
-- has not opened, and at the later one the first has closed

second-not-open-yet : ¬ (𝟏ᵣ ·ᵣ ιᵣ 3 ≾ᵣ [ 6 , 12 ])
second-not-open-yet (lo , _) = ≰! lo

first-closed-by-then : ¬ (𝟏ᵣ ·ᵣ ιᵣ 3 ·ᵣ opTime send ≾ᵣ [ 2 , 6 ])
first-closed-by-then (_ , hi) = ≰! hi

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ! [ 1 , 1 ]
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ! [ 1 , 1 ]
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ [ 1 , 1 ] ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- and no clause may drop its continuation: `𝟏ₑ ≾ₑ op-grade op ·ₑ ε''`
-- asks the clause's floor to be `0`, and an operation's is not

no-discarding : ¬ (𝟏ₑ ≾ₑ op-grade read ·ₑ 𝟏ₑ)
no-discarding (lo , _) = ≰! lo

------------------------------------------------------------------------
-- The greatest grade
--
-- `⌈ 0 , ∞ ⌉` bounds the elapsed time at neither end, so every
-- grade weakens to it. It does not absorb: sequencing keeps the lower
-- bound of whatever follows it.

everything-weakens : (ε : E) → ε ≾ₑ ⊤ₑ
everything-weakens = ≾-⊤ₑ

⊤-keeps-the-floor : (⊤ₑ ·ₑ [ 4 , 6 ]) ≡ (⌈ 4 , ∞ ⌉)
⊤-keeps-the-floor = refl
