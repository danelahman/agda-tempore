------------------------------------------------------------------------
-- Typed example computations at the grade of listed runs.             --
--                                                                     --
-- Effect grades and resource grades are both sets of timed traces, and --
-- the comparison is inclusion: a computation is graded by `Q` when     --
-- every run it may have *is* one of the traces `Q` lists. Nothing is   --
-- approximated -- a listed delay buys no work and a listed operation   --
-- permits nothing but itself -- so a grade has to name what it means.  --
--                                                                     --
-- Against the allowance order of `Traces.Timed.RightSided`, the        --
-- programs are the same and the side conditions are much harder to     --
-- meet. `unbox` needs the run that elapsed to be listed on the box     --
-- outright, so a permit covering a conditional has to name what each   --
-- branch does, and a `coerce` can only ever add runs to a list.        --
--                                                                     --
-- The comments inside the programs say what each former appends to the --
-- context its subcomputation is typed in: `⟨ ρ ⟩` a lock, `∷ A` a      --
-- binding. The locks between a box's binding and its `unbox` multiply  --
-- to the run that elapsed, and here that run has to be listed on the   --
-- box exactly.                                                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Subsets.RightSided where

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; NeTraces; ε; _∙_; ⌈_⌉; ⟨_⟩; ⟅_⟆; ⟅_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
  using (right-sided; holds; fails; holdsᵉ; failsᵉ)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them

opTime : Op → NeTraces
opTime o = ⟅ ⌈ o ⌉ ⟆

open import Syntax.Grades.Example.Worked.Typing.Core right-sided opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- At singleton grades sequencing still concatenates the runs, so the
-- grade of a computation is the run it makes, and the locks along it
-- are that run one event at a time.

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

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ uᵣ` asks the elapsed runs to be the empty one, so a reading is
-- usable only where no lock stands between its binding and its use.

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling = fails

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = fails

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆                     -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` adds runs to the list, and does nothing else: time buys no
-- work here, so the budgeted bound that the allowance order accepted is
-- not above the run that prompted it. The context is untouched.

listing-a-second-run :
  [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
listing-a-second-run =
  coerce holds (perform read ⋆ (perform write here (return ⋆)))

no-budgeting :
  ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆)
no-budgeting = fails

------------------------------------------------------------------------
-- Conditional branching
--
-- The union of two grades is still their join, so a conditional is
-- graded by the two branches' runs listed together -- and by nothing
-- shorter, there being no bound that covers both by costing more.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

six-ticks-buy-nothing : ¬ (opTime send ·ₑ uₑ ≾ₑ ⟅ ⟨ 6 ⟩ ⟆)
six-ticks-buy-nothing = fails

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

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
-- Unboxing: a permit that names its runs
--
-- The permit below lists two runs: taking a reading, and idling two
-- ticks. A claim is allowed after either of them -- that is, when the
-- locks in between multiply to one of the two -- and after nothing
-- else.

permit : R
permit = ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆

claim-after-sampling : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-sampling =
  box {ρ = permit} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (perform read ⋆                  -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds -- ∷ Reading
        (perform send here (return ⋆))))

claim-after-idling : [] ⊢C⦂ Unit ‼ ⟅ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
claim-after-idling =
  box {ρ = permit} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (delay 2                         -- ⟨ ⟅ ⟨ 2 ⟩ ⟆ ⟩
      (unbox (Tl-⟨⟩ Hd) holds        -- ∷ Reading
        (perform send here (return ⋆))))

handed-over : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box {ρ = permit} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (lam                             -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
       (perform read ⋆               -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box {ρ = permit} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (perform read ⋆                  -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds -- ∷ Reading
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- claiming it at once is not among them, the empty run not being listed

claiming-now-not-listed : ¬ (uᵣ ≾ᵣ permit)
claiming-now-not-listed = failsᵉ uᵣ permit

-- nor is one tick's idling, nor a reading followed by a store: a run
-- that is not listed is refused however little it costs

one-tick-not-listed : ¬ (uᵣ ·ᵣ of-natʳ 1 ≾ᵣ permit)
one-tick-not-listed = fails

storing-not-listed : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ permit)
storing-not-listed = fails

-- a permit that does list the empty run is claimable at once, with no
-- lock in between

listed-now : R
listed-now = ⟅ ε ∣ ⌈ read ⌉ ⟆

claiming-now : [] ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ⟆
claiming-now =
  box {ρ = listed-now} (const 42)    -- ∷ [ ⟅ ε ∣ ⌈ read ⌉ ⟆ ] Reading
    (unbox Hd (holdsᵉ uᵣ listed-now) -- ∷ Reading
      (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- A permit covering a conditional has to name what each branch does.

alternatives : R
alternatives = ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆

claimed-in-both-branches :
  [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
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

-- and dropping either run closes the branch that makes it

sampling-branch-needs-its-run : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ ⟅ ⌈ send ⌉ ⟆)
sampling-branch-needs-its-run = fails

transmitting-branch-needs-its-run : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ ⟅ ⌈ read ⌉ ⟆)
transmitting-branch-needs-its-run = fails

------------------------------------------------------------------------
-- Programs written at these lists
--
-- The permit claimed on both sides of an `if`: one branch takes the
-- reading it lists, the other idles the two ticks it lists, and the
-- conditional is graded by the two runs listed together.

permit-in-a-branch :
  [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
permit-in-a-branch =
  box {ρ = permit} (const 42)        -- ∷ [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce holds
              (perform read ⋆        -- ⟨ ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (delay 2               -- ⟨ ⟅ ⟨ 2 ⟩ ⟆ ⟩
                (unbox (Tl-⟨⟩ Hd) holds
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- both runs have to be on the permit: neither half of it covers the
-- other branch

idling-not-covered-by-the-reading : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ ⟅ ⌈ read ⌉ ⟆)
idling-not-covered-by-the-reading = fails

reading-not-covered-by-the-idling : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ ⟅ ⟨ 2 ⟩ ⟆)
reading-not-covered-by-the-idling = fails

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

-- no clause may drop its continuation: its grade lists runs that begin
-- with the operation, and returning at once makes the empty run

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = failsᵉ uₑ (op-grade read ·ₑ uₑ)
