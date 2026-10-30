------------------------------------------------------------------------
-- Typed example computations at the grade of upper bounds.           --
--                                                                    --
-- Effect grades and resource grades are both `[0, n ]`, "at most `n` --
-- time steps", and the operations are graded by their worst-case     --
-- time: read 1, write 3, send 6.                                     --
--                                                                    --
-- As an effect grade, `[0, n ]` is a deadline that a computation     --
-- meets, and `coerce` may relax it. As a resource grade it states    --
-- that at most `n` ticks have passed, so the premise `ρ' ≾ᵣ ρ` of    --
-- `unbox` (the elapsed grade lies within the grade of the box) makes --
-- `[ ρ ] A` a lease on a resource: claimable at once and while the   --
-- computation spends no more than `ρ`. A claim made too late is      --
-- refused; an upper bound imposes no release time, and no claim is   --
-- too early.                                                         --
--                                                                    --
-- The two consequences that are reversed relative to the lower       --
-- bounds, both checked below:                                        --
--                                                                    --
--   * the bound `ρ ≾ᵣ uᵣ` of `var` holds only at the unit, so a      --
--     reading goes stale after any activity, and a resource that     --
--     must survive is leased.                                        --
--                                                                    --
--   * a handler clause may discard its continuation: the grade of    --
--     the clause is a deadline, and returning at once meets every    --
--     deadline.                                                      --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. The locks are what the bound of `var` and the     --
-- premise of `unbox` are checked against; every lock other than the  --
-- unit makes a reading stale.                                        --
--                                                                    --
-- The endpoint ranges over the extended naturals, so every deadline  --
-- below is `[0, ↑ n ]`; `[0, ∞ ]` is the greatest grade and imposes  --
-- no deadline.                                                       --
------------------------------------------------------------------------

module ClosedCalculus.Examples.Typing.Time.RightSided where

open import Data.Bool.Base using (true; false)
import Data.List.Base as List
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Nullary using (¬_)

open import Data.Unit using (tt)

open import Util.Equality

open import Grades.Examples.Time.RightSided
  using (𝕀ᵣ; ℕ∞; ↑_; ∞; right-sided-intervals)
  renaming ([0,_] to ⌈0,_⌉)

-- every deadline written below is finite, and `⌈0, ∞ ⌉` is the greatest
-- grade, imposing no deadline at all

[0,_] : ℕ → 𝕀ᵣ
[0, n ] = ⌈0, ↑ n ⌉

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, graded by the time they may take at worst

open import Grades.Examples.Worked.Operations.Grading using (module Time-RightSided)
open Time-RightSided using (opTime) public

open import ClosedCalculus.Examples.Typing.Core right-sided-intervals opTime

open import Language.Comparisons using (Cmp; eq; ne; lt; le; gt; ge; less; equal; greater; holds)
open import ClosedCalculus.Syntax.Data spec using (compareᵈ)
open import ClosedCalculus.OperationalSemantics.State spec using (∅)
open import ClosedCalculus.OperationalSemantics.Reduction           spec using (⟨_,_⟩; _↝_; CMP)

------------------------------------------------------------------------
-- Effectful computations
--
-- The grade of a computation adds up the deadlines of the operations
-- along it, so it is the time the whole run may take at worst.

sampling : [] ⊢C⦂ Reading ‼ [0, 1 ]
sampling =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ [0, 4 ]
storing =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (perform write here              -- ⟨ [0, 3 ] ⟩ ∷ Unit
      (return ⋆))

-- take a reading and transmit it at once: the reading is used where it
-- was bound, with no lock in between, so `var` asks for nothing

relaying : [] ⊢C⦂ Unit ‼ [0, 7 ]
relaying =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (perform send here               -- ⟨ [0, 6 ] ⟩ ∷ Unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ [0, 7 ]
tagged-relaying =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `var` asks for `ρ ≾ᵣ uᵣ` at a non-eternal type, and the only grade
-- below `[0, 0 ]` is itself, so a reading is usable only where no lock
-- stands between its binding and its use.

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-durʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling = ≰!

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = ≰!

-- the identifier is eternal, so it crosses locks all the same

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ [0, 1 ]
carried-id =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` moves a computation up the order, and up means "allows
-- more". A deadline may always be relaxed and never tightened. It
-- leaves the context alone: only the grade moves.

relaxing-a-deadline : [] ⊢C⦂ Unit ‼ [0, 6 ]
relaxing-a-deadline = coerce ≤! (perform read ⋆ (perform write here (return ⋆)))

tightening-a-deadline : ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ) ≾ₑ [0, 3 ])
tightening-a-deadline = ≰!

------------------------------------------------------------------------
-- Conditional branching
--
-- Both branches are coerced to one grade, and here that grade is the
-- *larger* deadline: a conditional may take as long as its slower
-- branch. Neither branch locks the context.

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
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (if true
      `then coerce ≤! (perform send  here (return ⋆))
      `else coerce ≤! (perform write here (return ⋆)))

------------------------------------------------------------------------
-- Natural numbers
--
-- `caseℕ` binds the predecessor in its successor branch, and, as for
-- `if`, both branches are coerced to one grade.

is-zero : [] ⊢V⦂ Nat ⇒ Bool ‼ uₑ
is-zero = lam (caseℕ here `zero return true `succ return false)

predecessor : [] ⊢V⦂ Nat ⇒ Nat ‼ uₑ
predecessor = lam (caseℕ here `zero return zero `succ return here)

two-before-three : [] ⊢C⦂ Nat ‼ uₑ
two-before-three = predecessor · numeralᵛ 3

-- a count of pending transmissions: none costs nothing, otherwise the
-- reading is transmitted; the reading is bound before the branch, with no
-- lock in between, so `var` asks for nothing

transmitting-if-pending : [] ∷ Nat ∷ Reading ⊢C⦂ Unit ‼ [0, 6 ]
transmitting-if-pending =
  caseℕ eternal-var Natₑ (Tl-∷ Hd)
    `zero coerce ≤! (return ⋆)
    `succ perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)  -- ∷ Nat

-- a natural number is eternal: a count crosses a lock, here the one a
-- reading leaves

count-survives : [] ∷ Nat ⊢C⦂ Nat ‼ [0, 1 ]
count-survives =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (return (succ (eternal-var Natₑ (Tl-∷ (Tl-⟨⟩ Hd)))))

------------------------------------------------------------------------
-- Primitive recursion
--
-- `recℕ`'s step sees the ambient context behind `⟨ ⊤ᵣ ⟩`, binds the
-- predecessor, and, behind the lock of the recursion's own grade, the
-- result at the predecessor. The grade absorbs its own iteration,
-- `ε · ε ≾ ε`, which "at most `n` ticks" meets only at no tick and at no
-- deadline: a pure recursion is graded at the unit, a countdown at the
-- top.

-- addition, recursing on the first argument

add : [] ⊢V⦂ Nat ⇒ (Nat ⇒ Nat ‼ uₑ) ‼ uₑ
add =
  lam (return (lam
    (recℕ (eternal-var Natₑ (Tl-∷ Hd))
      (return here)
      (return (succ here))         -- ⟨ ⊤ᵣ ⟩ ∷ Nat ⟨ [0, 0 ] ⟩ ∷ Nat
      ≤!)))

two-plus-three : [] ⊢C⦂ Nat ‼ uₑ
two-plus-three =
  recℕ (numeralᵛ 2) (return (numeralᵛ 3)) (return (succ here)) ≤!

-- the predecessor, bound by the step, rebuilds the number

rebuild : [] ⊢V⦂ Nat ⇒ Nat ‼ uₑ
rebuild =
  lam (recℕ here
        (return zero)
        (return (succ (eternal-var Natₑ (Tl-∷ (Tl-⟨⟩ Hd)))))
        ≤!)

-- an identifier from outside the step: eternal, so it crosses the
-- barrier

tagging-each : [] ∷ NodeId ⊢C⦂ NodeId ‼ uₑ
tagging-each =
  recℕ (numeralᵛ 2)
    (return here)
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))))
    ≤!

-- a reading from outside the step is barred: the step's barrier is the
-- top, which lies above the unit

barrier-is-the-top : ⊤ᵣ ≡ ⌈0, ∞ ⌉
barrier-is-the-top = refl

reading-barred-from-step : ¬ (uᵣ ·ᵣ ⌈0, ∞ ⌉ ≾ᵣ uᵣ)
reading-barred-from-step ()

-- a countdown, a tick a step: graded at the top, which absorbs itself

countdown : [] ⊢V⦂ Nat ⇒ Unit ‼ ⊤ₑ
countdown =
  lam (recℕ here
        (coerce (≾-⊤ₑ uₑ) (return ⋆))
        (coerce (≾-⊤ₑ (of-durᵉ 1 ·ₑ uₑ)) (delay 1 (return ⋆)))
                                   -- ⟨ ⊤ᵣ ⟩ ∷ Nat ⟨ ⌈0, ∞ ⌉ ⟩ ∷ Unit
        (≾-⊤ₑ (⊤ₑ ·ₑ ⊤ₑ)))

three-ticks : [] ⊢C⦂ Unit ‼ ⊤ₑ
three-ticks = countdown · numeralᵛ 3

-- at any finite deadline a tick a step does not absorb itself

tick-a-step-overruns : ¬ ([0, 1 ] ·ₑ [0, 1 ] ≾ₑ [0, 1 ])
tick-a-step-overruns = ≰!

------------------------------------------------------------------------
-- Sums
--
-- `case+` binds the injected value in the branch its injection names,
-- and, as for `if`, both branches are coerced to one grade.

swap : ∀ {A B} → [] ⊢V⦂ (A |+| B) ⇒ (B |+| A) ‼ uₑ
swap = lam (case+ here `inl return (inr here) `inr return (inl here))

-- a reading is transmitted, an identifier stands for none and costs
-- nothing; the reading is bound by the branch itself, so `var` asks for
-- nothing

relaying-or-not : [] ∷ (Reading |+| NodeId) ⊢C⦂ Unit ‼ [0, 6 ]
relaying-or-not =
  case+ here
    `inl perform send here (return ⋆)  -- ∷ Reading
    `inr coerce ≤! (return ⋆)          -- ∷ NodeId

-- a sum is eternal when both summands are: a tagged identifier crosses
-- a lock, a sum that may hold a reading does not

tag-survives : [] ∷ (NodeId |+| Unit) ⊢C⦂ (NodeId |+| Unit) ‼ [0, 1 ]
tag-survives =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (return (eternal-var (nodeid-eternal |+|ₑ Unitₑ) (Tl-∷ (Tl-⟨⟩ Hd))))

reading-or-tag-not-eternal : ¬ Eternal (Reading |+| NodeId)
reading-or-tag-not-eternal (r |+|ₑ _) = reading-not-eternal r

------------------------------------------------------------------------
-- Lists
--
-- `caseL` binds the head and then the tail in its `cons` branch, and,
-- as for `if`, both branches are coerced to one grade.

-- the first pending reading is transmitted, an empty list costs nothing;
-- the head is bound by the branch itself, so `var` asks for nothing

transmitting-the-first : [] ∷ |List| Reading ⊢C⦂ Unit ‼ [0, 6 ]
transmitting-the-first =
  caseL here
    `nil coerce ≤! (return ⋆)
    `cons perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)
                                     -- ∷ Reading ∷ |List| Reading

-- a list is eternal when its elements are: identifiers cross a lock, a
-- list that may hold readings does not

ids-survive : [] ∷ |List| NodeId ⊢C⦂ |List| NodeId ‼ [0, 1 ]
ids-survive =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (return (eternal-var (|List|ₑ nodeid-eternal) (Tl-∷ (Tl-⟨⟩ Hd))))

readings-not-eternal : ¬ Eternal (|List| Reading)
readings-not-eternal (|List|ₑ r) = reading-not-eternal r

------------------------------------------------------------------------
-- Primitive recursion on lists
--
-- `recL`'s step sees the ambient context behind `⟨ ⊤ᵣ ⟩`, binds the head
-- and the tail, and, behind the lock of the recursion's own grade, the
-- result at the tail. As for `recℕ`, the grade absorbs its own
-- iteration: a pure recursion is graded at the unit, one that idles at
-- each element at the top.

-- the length, whatever the elements are

length : ∀ {A} → [] ⊢V⦂ |List| A ⇒ Nat ‼ uₑ
length =
  lam (recL here
        (return zero)
        (return (succ here))         -- ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A ⟨ [0, 0 ] ⟩ ∷ Nat
        ≤!)

three-readings-long : [] ⊢C⦂ Nat ‼ uₑ
three-readings-long =
  length {Reading} · cons (const 1) (cons (const 2) (cons (const 3) nil))

-- a pure map: each count is incremented; a count is eternal, so the head
-- crosses the result's lock

incrementing : [] ⊢V⦂ |List| Nat ⇒ |List| Nat ‼ uₑ
incrementing =
  lam (recL here
        (return nil)
        (return (cons (succ (eternal-var Natₑ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))) here))
        ≤!)

-- pacing a list, a tick an element: graded at the top, which absorbs
-- itself

pacing : ∀ {A} → [] ⊢V⦂ |List| A ⇒ Unit ‼ ⊤ₑ
pacing =
  lam (recL here
        (coerce (≾-⊤ₑ uₑ) (return ⋆))
        (coerce (≾-⊤ₑ (of-durᵉ 1 ·ₑ uₑ)) (delay 1 (return ⋆)))
                                     -- ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A ⟨ ⌈0, ∞ ⌉ ⟩ ∷ Unit
        (≾-⊤ₑ (⊤ₑ ·ₑ ⊤ₑ)))

-- The head is bound before the result's lock, so the step reads it only
-- after the recursion at the tail has run. A reading is a head the step
-- may use when that takes no time: the latest reading, at the unit.

latest : [] ⊢V⦂ |List| Reading ⇒ (Reading |+| Unit) ‼ uₑ
latest =
  lam (recL here
        (return (inr ⋆))
        (return (inl (fresh-var ≤! (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))))
                                     -- ⟨ ⊤ᵣ ⟩ ∷ Reading ∷ |List| Reading
                                     --   ⟨ [0, 0 ] ⟩ ∷ (Reading |+| Unit)
        ≤!)

-- behind the lock of a recursion that may take time, the head is stale

head-stale-behind-the-top : ¬ (uᵣ ·ᵣ mapᵉ ⊤ₑ ≾ᵣ uᵣ)
head-stale-behind-the-top ()

------------------------------------------------------------------------
-- Comparisons
--
-- `cmp` compares two values of one eternal type and returns the truth
-- of the relation, taking no time. Identifiers are ordered as their
-- numbers; the data built from eternal types, lexicographically.

-- two identifiers, bound together, compared at once

same-node : [] ∷ NodeId ∷ NodeId ⊢C⦂ Bool ‼ uₑ
same-node =
  cmp eq (eternal-var nodeid-eternal (Tl-∷ Hd)) here nodeid-eternal

-- an identifier is eternal, so it is compared after a reading all the same

below-after-reading : [] ∷ NodeId ⊢C⦂ Bool ‼ [0, 1 ]
below-after-reading =
  perform read ⋆                     -- ⟨ [0, 1 ] ⟩ ∷ Reading
    (cmp lt (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))) (const 7) nodeid-eternal)

-- a reading is not eternal, so no comparison of readings is typed

readings-not-compared : ¬ Eternal Reading
readings-not-compared = reading-not-eternal

-- the comparison decides the branch: transmit the reading only to a
-- node above the threshold

transmitting-above : [] ∷ NodeId ∷ Reading ⊢C⦂ Unit ‼ [0, 6 ]
transmitting-above =
  cmp gt (eternal-var nodeid-eternal (Tl-∷ Hd)) (const 3) nodeid-eternal
    ⨟                                -- ⟨ [0, 0 ] ⟩ ∷ Bool
  coerce ≤!
    (if here
      `then perform send (fresh-var ≤! (Tl-∷ (Tl-⟨⟩ Hd))) (return ⋆)
      `else coerce ≤! (return ⋆))

-- The order on data, computed: numerals as numbers, lists and pairs
-- lexicographically, `inl` before `inr`, identifiers as their numbers.

two-below-three : compareᵈ Natₑ 2 3 ≡ less
two-below-three = refl

shorter-prefix-first : compareᵈ (|List|ₑ Natₑ) (1 List.∷ 2 List.∷ List.[])
                                       (1 List.∷ 2 List.∷ 0 List.∷ List.[]) ≡ less
shorter-prefix-first = refl

first-difference-decides : compareᵈ (|List|ₑ Natₑ) (1 List.∷ 5 List.∷ List.[])
                                           (2 List.∷ 0 List.∷ List.[]) ≡ less
first-difference-decides = refl

pairs-by-first-then-second : compareᵈ (Natₑ |×|ₑ Boolₑ) (1 , true) (1 , false) ≡ greater
pairs-by-first-then-second = refl

inl-before-inr : compareᵈ (Natₑ |+|ₑ Unitₑ) (inj₁ 9) (inj₂ tt) ≡ less
inl-before-inr = refl

identifiers-as-numbers : compareᵈ nodeid-eternal 4 4 ≡ equal
identifiers-as-numbers = refl

-- each relation is read off the one outcome

at-most-of-equal : holds le (compareᵈ nodeid-eternal 4 4) ≡ true
at-most-of-equal = refl

differ-of-less : holds ne (compareᵈ Natₑ 2 3) ≡ true
differ-of-less = refl

-- `CMP` reduces a comparison to the returned outcome, reading the operands'
-- data off the values

two-below-three-reduces : ⟨ ∅ , cmp lt (numeralᵛ 2) (numeralᵛ 3) Natₑ ⟩
                        ↝ ⟨ ∅ , return true ⟩
two-below-three-reduces = CMP

------------------------------------------------------------------------
-- Unboxing: a lease that expires
--
-- `unbox`'s premise `elapsed ≾ᵣ ρ` reads `elapsed ≤ ρ` here: the box
-- may be claimed while what the computation has spent -- the product of
-- the locks between the box's binding and the claim -- is still within
-- what the box allows. The resource below is leased for six ticks'
-- worth of work.

-- claimed at once, with no lock in between

claiming-now : [] ⊢C⦂ Unit ‼ [0, 6 ]
claiming-now =
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (unbox Hd ≤! (<:ᵛ-refl _)        -- ∷ Reading
      (perform send here (return ⋆)))

-- claimed after idling two ticks of the six

claim-after-idling : [] ⊢C⦂ Unit ‼ [0, 8 ]
claim-after-idling =
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (delay 2                         -- ⟨ [0, 2 ] ⟩
      (unbox (Tl-⟨⟩ Hd) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- and after taking a reading, which spends one

claim-after-sampling : [] ⊢C⦂ Unit ‼ [0, 7 ]
claim-after-sampling =
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [0, 1 ] ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- a transmission and a reading spend seven, which the lease does not
-- cover, so the claim is refused

lease-expired : ¬ (uᵣ ·ᵣ opTime send ·ᵣ opTime read ≾ᵣ [0, 6 ])
lease-expired = ≰!

-- idling spends the lease just as working does

idling-spends-it : ¬ (uᵣ ·ᵣ of-durʳ 7 ≾ᵣ [0, 6 ])
idling-spends-it = ≰!

-- handing a leased resource to a function, which claims it itself

handed-over : [] ⊢C⦂ Unit ‼ [0, 7 ]
handed-over =
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (lam                             -- ∷ [ [0, 6 ] ] Reading
       (perform read ⋆               -- ⟨ [0, 1 ] ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

-- claiming the resource and then choosing what to transmit -- the
-- claimed reading or one taken along the way -- with both branches
-- making the same run

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ [0, 7 ]
either-way =
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [0, 1 ] ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
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
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (if true
      `then coerce ≤!
              (perform read ⋆        -- ⟨ [0, 1 ] ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce ≤!
              (perform send (const 0)
                                     -- ⟨ [0, 6 ] ⟩ ∷ Unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing locks its continuation by the grade the first part is
-- *typed at*. A `coerce` there can only take claims away: coercing
-- relaxes the deadline, so the lock grows and the lease is spent
-- against a larger figure.

-- a reading spends one of the four the lease allows

claim-after-a-reading : [] ⊢C⦂ Unit ‼ [0, 7 ]
claim-after-a-reading =
  box [0, 4 ] (const 42)             -- ∷ [ [0, 4 ] ] Reading
    ((perform read ⋆ (return here))
      ⨟                              -- ⟨ [0, 1 ] ⟩ ∷ Reading
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- relaxing that reading's deadline to six spends six of them, and the
-- lease does not cover it

coercing-closes-it : ¬ (uᵣ ·ᵣ [0, 6 ] ≾ᵣ [0, 4 ])
coercing-closes-it = ≰!

-- the same program with the coercion, against a lease long enough for
-- what it claims to have spent

claim-after-a-coerced-reading : [] ⊢C⦂ Unit ‼ [0, 12 ]
claim-after-a-coerced-reading =
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (coerce {ε' = [0, 6 ]} ≤! (perform read ⋆ (return here))
      ⨟                              -- ⟨ [0, 6 ] ⟩ ∷ Reading
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Programs written at these intervals
--
-- What a reading cannot do here, a lease can: the run below takes a
-- reading, idles, and transmits a leased resource, the reading it took
-- itself having gone stale under the idling lock.

carrying-a-lease : [] ⊢C⦂ Unit ‼ [0, 9 ]
carrying-a-lease =
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [0, 1 ] ⟩ ∷ Reading
      (delay 2                       -- ⟨ [0, 2 ] ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

-- the reading taken along the way is not available at that same point

reading-is-not : ¬ (uᵣ ·ᵣ opTime read ·ᵣ of-durʳ 2 ≾ᵣ uᵣ)
reading-is-not = ≰!

-- a lease long enough to cover a transmission as well, spent down to
-- seven of its nine by the time the claim is made

longer-lease : [] ⊢C⦂ Unit ‼ [0, 13 ]
longer-lease =
  box [0, 9 ] (const 42)             -- ∷ [ [0, 9 ] ] Reading
    (perform read ⋆                  -- ⟨ [0, 1 ] ⟩ ∷ Reading
      (perform send (const 0)        -- ⟨ [0, 6 ] ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
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
  box [0, 6 ] (const 42)             -- ∷ [ [0, 6 ] ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then delay 2                  -- ⟨ [0, 2 ] ⟩
              (unbox (Tl-⟨⟩ Hd) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                (perform send here (return ⋆)))
      `else coerce ≤!
              (perform read ⋆        -- ⟨ [0, 1 ] ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) ≤! (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- the claim has to be made before the transmission and not after it:
-- the sampling branch spends one of the six, and transmitting first
-- would spend seven -- `short-lease-run-out` above

claim-before-transmitting : uᵣ ·ᵣ opTime read ≾ᵣ [0, 6 ]
claim-before-transmitting = ≤!

------------------------------------------------------------------------
-- Effect handling
--
-- Handling locks its `in` part by the handled computation's grade,
-- exactly as sequencing does.

forwarded : [] ⊢C⦂ Reading ‼ [0, 1 ]
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ [0, 1 ] ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ [0, 1 ]
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ [0, 1 ] ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- a clause may drop its continuation here: it is graded at a deadline
-- the operation and the resumption would have to meet, and returning at
-- once meets it

nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits read  ⌈0, ↑ n ⌉ = z≤n
nothing-fits read  ⌈0, ∞ ⌉   = tt
nothing-fits write ⌈0, ↑ n ⌉ = z≤n
nothing-fits write ⌈0, ∞ ⌉   = tt
nothing-fits send  ⌈0, ↑ n ⌉ = z≤n
nothing-fits send  ⌈0, ∞ ⌉   = tt

-- the operations are suppressed, and the grade the handled computation
-- is typed at is unchanged by that

suppressed : [] ⊢C⦂ Unit ‼ [0, 4 ]
suppressed =
  handle perform read ⋆ (perform write here (return ⋆))
    `with discarding {[]} nothing-fits
    `in                              -- ⟨ [0, 4 ] ⟩ ∷ Unit
      (return ⋆)

------------------------------------------------------------------------
-- The greatest grade
--
-- `⌈0, ∞ ⌉` imposes no deadline, so every grade weakens to it, and it
-- absorbs: nothing sequenced after an unbounded computation is bounded.

everything-weakens : (ε : E) → ε ≾ₑ ⊤ₑ
everything-weakens = ≾-⊤ₑ

⊤-absorbs : (⊤ₑ ·ₑ [0, 4 ]) ≡ ⊤ₑ
⊤-absorbs = refl

-- and unlike the unit it is not a deadline any reading survives

reading-stale-at-⊤ : ¬ (uᵣ ·ᵣ ⊤ᵣ ≾ᵣ uᵣ)
reading-stale-at-⊤ ()

-- so no handler clause here may close over a reading: the bound
-- `reporting` asks for fails at the barrier already, whatever the
-- clause spends past it

no-reporting : (op : Op) → (ε'' : E)
             → ¬ (uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ uᵣ)
no-reporting op ε'' bound =
  reading-stale-at-⊤
    (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ} {op-grade op}
      (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op} {ε''} bound))
