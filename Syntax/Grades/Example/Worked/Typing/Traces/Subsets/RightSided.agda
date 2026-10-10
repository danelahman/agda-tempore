------------------------------------------------------------------------
-- Typed example computations at the grade of listed runs.            --
--                                                                    --
-- Effect grades and resource grades are both sets of timed traces,   --
-- and the comparison is inclusion: a computation is graded by `Q`    --
-- when every run it may have is one of the traces that `Q` lists. A  --
-- listed delay pays for no operations and a listed operation permits --
-- only itself, so a grade lists the runs it permits.                 --
--                                                                    --
-- The programs are those of the allowance order of                   --
-- `Traces.Timed.RightSided`, with side conditions that hold less     --
-- often. `unbox` requires the elapsed run to be listed on the box,   --
-- so a permit covering a conditional lists the run of each branch,   --
-- and `coerce` can only add runs to a list.                          --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. The locks between the binding of a box and its    --
-- `unbox` multiply to the elapsed run, which must be listed on the   --
-- box.                                                               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Subsets.RightSided where

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; ε; _∙_; ⌈_⌉; ⟨_⟩; ⟅_⟆; ⟅_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
  using (right-sided; Permits; permitting_; any-run;
         holds; fails; holdsᵉ; failsᵉ)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them

opTime : Op → Permits
opTime o = permitting ⟅ ⌈ o ⌉ ⟆

open import Syntax.Grades.Example.Worked.Typing.Core right-sided opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- At singleton grades sequencing still concatenates the runs, so the
-- grade of a computation is the run it makes, and the locks along it
-- are that run one event at a time.

sampling : [] ⊢C⦂ Reading ‼ permitting ⟅ ⌈ read ⌉ ⟆
sampling =
  perform read ⋆         -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing =
  perform read ⋆         -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform write here  -- ⟨ permitting ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
relaying =
  perform read ⋆         -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform send here   -- ⟨ permitting ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
tagged-relaying =
  perform read ⋆         -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                         -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ uᵣ` asks the elapsed runs to be the empty one, so a reading is
-- usable only where no lock stands between its binding and its use.

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-durʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling = fails

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = fails

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ permitting ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆         -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` adds runs to the list and does nothing else: time pays for
-- no operation, and the budgeted bound accepted by the allowance order
-- is not above the run in question. The context is untouched.

listing-a-second-run :
  [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
listing-a-second-run =
  coerce holds (perform read ⋆ (perform write here (return ⋆)))

no-budgeting :
  ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ permitting ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆)
no-budgeting = fails

------------------------------------------------------------------------
-- Conditional branching
--
-- The union of two grades is still their join, so a conditional is
-- graded by the two branches' runs listed together -- and by nothing
-- shorter, there being no bound that covers both by costing more.

branching :
  [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ permitting ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

six-ticks-buy-nothing : ¬ (opTime send ·ₑ uₑ ≾ₑ permitting ⟅ ⟨ 6 ⟩ ⟆)
six-ticks-buy-nothing = fails

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

either-reading :
  [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ permitting ⟅ ⌈ send ⌉ ⟆
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

sampling-then-branching :
  [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
sampling-then-branching =
  perform {ε = permitting ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆} read ⋆
                         -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (if true
      `then coerce holds (perform send  here (return ⋆))
      `else coerce holds (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a permit that names its runs
--
-- The permit below lists two runs: taking a reading, and idling two
-- ticks. A claim is allowed after either of them -- that is, when the
-- locks in between multiply to one of the two -- and after nothing
-- else.

permit : R
permit = permitting ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆

claim-after-sampling : [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-sampling =
  box {ρ = permit} (const 42)  -- ∷ [ permitting ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (perform read ⋆      -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

claim-after-idling : [] ⊢C⦂ Unit ‼ permitting ⟅ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
claim-after-idling =
  box {ρ = permit} (const 42)  -- ∷ [ permitting ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (delay 2             -- ⟨ permitting ⟅ ⟨ 2 ⟩ ⟆ ⟩
      (unbox (Tl-⟨⟩ Hd) holds (<:ᵛ-refl _)
                               -- ∷ Reading
        (perform send here (return ⋆))))

handed-over : [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box {ρ = permit} (const 42)  -- ∷ [ permitting ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (lam                 -- ∷ [ permitting ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
       (perform read ⋆   -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                         -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box {ρ = permit} (const 42)  -- ∷ [ permitting ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (perform read ⋆      -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- claiming it at once is not among them, the empty run not being listed

claiming-now-not-listed : ¬ (uᵣ ≾ᵣ permit)
claiming-now-not-listed = failsᵉ uᵣ permit

-- nor is one tick's idling, nor a reading followed by a store: a run
-- that is not listed is refused however little it costs

one-tick-not-listed : ¬ (uᵣ ·ᵣ of-durʳ 1 ≾ᵣ permit)
one-tick-not-listed = fails

storing-not-listed : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ permit)
storing-not-listed = fails

-- a permit that does list the empty run is claimable at once, with no
-- lock in between

listed-now : R
listed-now = permitting ⟅ ε ∣ ⌈ read ⌉ ⟆

claiming-now : [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ send ⌉ ⟆
claiming-now =
  box {ρ = listed-now} (const 42)  -- ∷ [ permitting ⟅ ε ∣ ⌈ read ⌉ ⟆ ] Reading
    (unbox Hd (holdsᵉ uᵣ listed-now) (<:ᵛ-refl _)
                                     -- ∷ Reading
      (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- A permit covering a conditional has to name what each branch does.

alternatives : R
alternatives = permitting ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆

claimed-in-both-branches :
  [] ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
claimed-in-both-branches =
  box {ρ = alternatives} (const 42)
                         -- ∷ [ permitting ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ ] Reading
    (if true
      `then coerce holds
              (perform read ⋆  -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                         -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (perform send (const 0)
                         -- ⟨ permitting ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                         -- ∷ Reading
                  (perform send here (return ⋆)))))

-- and dropping either run closes the branch that makes it

sampling-branch-needs-its-run :
  ¬ (uᵣ ·ᵣ opTime read ≾ᵣ permitting ⟅ ⌈ send ⌉ ⟆)
sampling-branch-needs-its-run = fails

transmitting-branch-needs-its-run :
  ¬ (uᵣ ·ᵣ opTime send ≾ᵣ permitting ⟅ ⌈ read ⌉ ⟆)
transmitting-branch-needs-its-run = fails

------------------------------------------------------------------------
-- Programs written at these lists
--
-- The permit claimed on both sides of an `if`: one branch takes the
-- reading it lists, the other idles the two ticks it lists, and the
-- conditional is graded by the two runs listed together.

permit-in-a-branch :
  [] ∷ Bool ⊢C⦂ Unit ‼ permitting ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
permit-in-a-branch =
  box {ρ = permit} (const 42)  -- ∷ [ permitting ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce holds
              (perform read ⋆  -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                         -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (delay 2   -- ⟨ permitting ⟅ ⟨ 2 ⟩ ⟆ ⟩
                (unbox (Tl-⟨⟩ Hd) holds (<:ᵛ-refl _)
                         -- ∷ Reading
                  (perform send here (return ⋆)))))

-- both runs have to be on the permit: neither half of it covers the
-- other branch

idling-not-covered-by-the-reading :
  ¬ (uᵣ ·ᵣ of-durʳ 2 ≾ᵣ permitting ⟅ ⌈ read ⌉ ⟆)
idling-not-covered-by-the-reading = fails

reading-not-covered-by-the-idling :
  ¬ (uᵣ ·ᵣ opTime read ≾ᵣ permitting ⟅ ⟨ 2 ⟩ ⟆)
reading-not-covered-by-the-idling = fails

------------------------------------------------------------------------
-- Effect handling
--
-- Handling locks its `in` part by the handled computation's grade,
-- exactly as sequencing does.

forwarded : [] ⊢C⦂ Reading ‼ permitting ⟅ ⌈ read ⌉ ⟆
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                  -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ permitting ⟅ ⌈ read ⌉ ⟆
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                  -- ⟨ permitting ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: its grade lists runs that begin
-- with the operation, and returning at once makes the empty run

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = failsᵉ uₑ (op-grade read ·ₑ uₑ)
