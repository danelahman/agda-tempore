------------------------------------------------------------------------
-- Typed example computations at the grade of trace allowances.       --
--                                                                    --
-- Effect grades and resource grades are both sets of timed traces at --
-- the allowance order, and each operation is graded by the one-event --
-- run that performs it. A grade is a set of bounds, and a            --
-- computation lies below it when each of its runs stays within one   --
-- of them: the operations of the bound are permissions and its       --
-- delays a budget, spent on idling and on operations the bound does  --
-- not list, at `costʰⁱ` (read 1, write 3, send 6).                   --
--                                                                    --
-- The grade records *which* operations a run performed and *where*.  --
-- The premise of `unbox` requires the elapsed run to be one the box  --
-- permits, and a claim can be refused for performing the wrong       --
-- operations, or the right operations in the wrong order, rather     --
-- than for taking too long. Both refusals are shown below.           --
--                                                                    --
-- Sub-effecting is the same order, and a union is a join, so a       --
-- conditional is graded by the union of the grades of its branches.  --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. The locks between the binding of a box and its    --
-- `unbox` multiply to the run that the premise compares with the     --
-- allowance of the box, so the order of the locks is part of what is --
-- checked.                                                           --
------------------------------------------------------------------------

module ClosedCalculus.Examples.Typing.Traces.Timed.RightSided where

open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans;
         costʰⁱ; costʰⁱ-pos; ε; _∙_; ⌈_⌉; ⟨_⟩)

open import Grades.Examples.Worked.Traces.Timed.RightSided
  using (right-sided; Bounds; within_; unbounded; holds; fails;
         Antichain; ⟅_⟆; ⟅_∣_⟆; ≾-⊥)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them

open import Grades.Examples.Worked.Operations.Grading using (module Traces-Timed-RightSided)
open Traces-Timed-RightSided using (opTime₀; opTime) public

open import ClosedCalculus.Examples.Typing.Core right-sided opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- Sequencing is the language product, so at singleton grades the grade
-- of a computation is the run it makes -- and the locks along it are
-- that run, one event at a time.

sampling : [] ⊢C⦂ Reading ‼ within ⟅ ⌈ read ⌉ ⟆
sampling =
  perform read ⋆     -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing =
  perform read ⋆     -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform write here  -- ⟨ within ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
relaying =
  perform read ⋆     -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform send here  -- ⟨ within ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
tagged-relaying =
  perform read ⋆     -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                     -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `var`'s bound is `ρ ≾ᵣ uᵣ`, and the unit permits nothing but the
-- empty run. So a reading is usable only where no lock stands between
-- its binding and its use.

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-durʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling = fails

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = fails

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ within ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆     -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves up the order: an operation becomes a delay long enough
-- to cover it, and a delay grows. Neither direction is reversible, and
-- the context is untouched.

exact-run-to-budget : [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆
exact-run-to-budget =
  coerce holds (perform read ⋆ (perform write here (return ⋆)))

budget-back-to-the-run :
  ¬ (opTime read ·ₑ (of-durᵉ 3 ·ₑ uₑ) ≾ₑ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
budget-back-to-the-run = fails

------------------------------------------------------------------------
-- Conditional branching
--
-- The union of two grades is their join, so the grade of the
-- conditional lists what each branch does. Neither branch locks the
-- context.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ within ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

-- neither branch's own grade will do for the other, an operation being
-- no payment for a different one

transmitting-is-not-storing : ¬ (opTime send ·ₑ uₑ ≾ₑ within ⟅ ⌈ write ⌉ ⟆)
transmitting-is-not-storing = fails

storing-is-not-transmitting : ¬ (opTime write ·ₑ uₑ ≾ₑ within ⟅ ⌈ send ⌉ ⟆)
storing-is-not-transmitting = fails

-- a budget covering the costlier branch covers both, time paying for
-- any operation that costs no more

timed-branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ within ⟅ ⟨ 6 ⟩ ⟆
timed-branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce holds (perform send  here (return ⋆))
    `else coerce holds (perform write here (return ⋆))

-- five ticks do not pay for a transmission

five-ticks-are-short : ¬ (opTime send ·ₑ uₑ ≾ₑ within ⟅ ⟨ 5 ⟩ ⟆)
five-ticks-are-short = fails

-- an `if` over data alone: both branches make the same run, so neither
-- is coerced

either-reading :
  [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ within ⟅ ⌈ send ⌉ ⟆
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

sampling-then-branching :
  [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
sampling-then-branching =
  perform {ε = within ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆} read ⋆
                     -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (if true
      `then coerce holds (perform send  here (return ⋆))
      `else coerce holds (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing: a permit for a particular run
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`: the locks between the box's
-- binding and the claim multiply to the run the computation made, and
-- it has to be one the box permits. The permit below names a reading
-- and budgets three ticks for whatever else happens.

permit : R
permit = within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆

-- the reading the permit names, two ticks of its budget, and the empty
-- run all keep it open

claim-after-sampling : [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-sampling =
  box permit (const 42)        -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ] Reading
    (perform read ⋆  -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

claim-after-idling : [] ⊢C⦂ Unit ‼ within ⟅ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
claim-after-idling =
  box permit (const 42)        -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ] Reading
    (delay 2         -- ⟨ within ⟅ ⟨ 2 ⟩ ⟆ ⟩
      (unbox (Tl-⟨⟩ Hd) holds (<:ᵛ-refl _)
                               -- ∷ Reading
        (perform send here (return ⋆))))

claiming-now : [] ⊢C⦂ Unit ‼ within ⟅ ⌈ send ⌉ ⟆
claiming-now =
  box permit (const 42)        -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ] Reading
    (unbox Hd holds (<:ᵛ-refl _)
                     -- ∷ Reading
      (perform send here (return ⋆)))

storing-keeps-it-open : uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ permit
storing-keeps-it-open = holds

-- a transmission closes it: it is not named, and six ticks is more than
-- the permit budgets

transmitting-closes-it : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ permit)
transmitting-closes-it = fails

transmitting-after-the-reading-too :
  ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ permit)
transmitting-after-the-reading-too = fails

handed-over : [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box permit (const 42)        -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ] Reading
    (lam             -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ] Reading
       (perform read ⋆  -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box permit (const 42)        -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ] Reading
    (perform read ⋆  -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                                     -- ∷ Reading
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- A permit may list alternatives, and then each branch need only match
-- one of them. Listing the reading and the transmission separately puts
-- the resource within both branches' reach.

alternatives : R
alternatives = within ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆

claimed-in-both-branches :
  [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
claimed-in-both-branches =
  box alternatives (const 42)
                     -- ∷ [ within ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ ] Reading
    (if true
      `then coerce holds
              (perform read ⋆  -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (perform send (const 0)
                     -- ⟨ within ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- with the reading alone permitted, only one branch reaches it

sampling-branch-reaches : uᵣ ·ᵣ opTime read ≾ᵣ within ⟅ ⌈ read ⌉ ⟆
sampling-branch-reaches = holds

transmitting-branch-does-not : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ within ⟅ ⌈ read ⌉ ⟆)
transmitting-branch-does-not = fails

------------------------------------------------------------------------
-- Programs written at these allowances
--
-- The permit claimed on both sides of an `if`: one branch takes the
-- reading it names and transmits what it unboxes, the other spends two
-- of its three ticks idling and stores it. The conditional is graded by
-- the union of the two runs, which are incomparable, so both are listed.

permit-in-a-branch :
  [] ∷ Bool ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 2 ⟩ ∙ ⌈ write ⌉ ⟆
permit-in-a-branch =
  box permit (const 42)        -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆ ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce holds
              (perform read ⋆  -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds (<:ᵛ-refl _)
                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce holds
              (delay 2  -- ⟨ within ⟅ ⟨ 2 ⟩ ⟆ ⟩
                (unbox (Tl-⟨⟩ Hd) holds (<:ᵛ-refl _)
                     -- ∷ Reading
                  (perform write here (return ⋆)))))

-- a third branch transmitting before the claim is not available:
-- `transmitting-closes-it` above is what it would need

-- Where the budget sits is part of the permit. This one names a
-- reading, then budgets three ticks, then names a transmission, and the
-- run below spends its store inside that window -- which the locks show
-- in the order the permit reads them.

scheduled : R
scheduled = within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ∙ ⌈ send ⌉ ⟆

in-order :
  [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
in-order =
  box scheduled (const 42)
                     -- ∷ [ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ∙ ⌈ send ⌉ ⟆ ] Reading
    (perform read ⋆  -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (perform write here  -- ⟨ within ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
        (perform send (const 0)  -- ⟨ within ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
          (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))))) holds (<:ᵛ-refl _)
                     -- ∷ Reading
            (perform send here (return ⋆))))))

-- the same three operations with the store after the transmission
-- overrun the permit, budget not crossing an operation it names

out-of-order :
  ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ·ᵣ opTime write ≾ᵣ scheduled)
out-of-order = fails

------------------------------------------------------------------------
-- Effect handling
--
-- Handling locks its `in` part by the handled computation's grade,
-- exactly as sequencing does.

forwarded : [] ⊢C⦂ Reading ‼ within ⟅ ⌈ read ⌉ ⟆
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in              -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ within ⟅ ⌈ read ⌉ ⟆
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in              -- ⟨ within ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- a clause may drop its continuation: the empty run stays within every
-- allowance, and within `unbounded`, so the coercion a
-- discarding clause needs always exists

nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits op ε'' = ≾-⊥ (op-grade op ·ₑ ε'')

suppressed : [] ⊢C⦂ Unit ‼ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
suppressed =
  handle perform read ⋆ (perform write here (return ⋆))
    `with discarding {[]} nothing-fits
    `in              -- ⟨ within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆)
