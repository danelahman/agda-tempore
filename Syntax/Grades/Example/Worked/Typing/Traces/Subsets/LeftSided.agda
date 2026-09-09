------------------------------------------------------------------------
-- Typed example computations at the grade of demanded runs.           --
--                                                                     --
-- A grade `P` is read against the runs `X` a computation may have as   --
-- `P ⊆ X`: every listed trace is a run it can exhibit. The set is read --
-- *conjunctively*, so weakening drops members and `{ ε }` -- demanding --
-- only that stopping is possible -- is the greatest grade.             --
--                                                                     --
-- The calculus meets this grade at its most rigid. Every operation is  --
-- graded by a singleton, products of singletons are singletons, and a  --
-- grade below a singleton is a non-empty subset of it, hence that      --
-- singleton again: so every computation's grade is exactly its run and --
-- `coerce` has nothing to do. `unbox` inherits that -- a box is        --
-- claimable only after precisely the run it names -- and `if` inherits --
-- something sharper still: `no-common-grade` below shows that no grade --
-- whatever types a conditional whose branches perform different        --
-- operations, since the two coercions would make one non-empty set a   --
-- subset of two disjoint singletons. What `if` can still do here is    --
-- branch over *data*, both branches making the same run.               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Subsets.LeftSided where

open import Data.Empty using (⊥)
open import Data.List.Base using () renaming (_∷_ to _∷ˡ_; [] to []ˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ)
open import Data.Product using (Σ; _,_)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_;
         Trace; NeTraces; neTraces; traces; ε; _∙_; ⌈_⌉; ⟨_⟩; ⟅_⟆; ⟅_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Subsets.LeftSided
  using (left-sided; holds; fails; holdsᵉ; failsᵉ)

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ using (∈-⊑)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them

opTime : Op → NeTraces
opTime o = ⟅ ⌈ o ⌉ ⟆

open import Syntax.Grades.Example.Worked.Typing.Core left-sided opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- The grade of a computation is the one run it makes, demanded.

sampling : [] ⊢C⦂ Reading ‼ ⟅ ⌈ read ⌉ ⟆
sampling = perform read ⋆ (return here)

storing : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing = perform read ⋆ (perform write here (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
relaying = perform read ⋆ (perform send here (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
tagged-relaying =
  perform read ⋆
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ uᵣ` asks the empty run to be among the elapsed ones, which it
-- is only where nothing happened.

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = fails

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling = fails

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆ (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- Weakening drops demands, so a grade below a singleton is a non-empty
-- subset of it: the singleton itself. A deterministic computation
-- therefore has nowhere to be coerced to.

adding-a-demand : ¬ (opTime read ·ₑ uₑ ≾ₑ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆)
adding-a-demand = fails

trading-work-for-time : ¬ (opTime read ·ₑ uₑ ≾ₑ ⟅ ⟨ 1 ⟩ ⟆)
trading-work-for-time = fails

------------------------------------------------------------------------
-- Conditional branching
--
-- No grade at all types a conditional whose branches perform different
-- operations: a common grade would have to be a non-empty subset of
-- both branches' singletons.

-- a non-empty set has a member

member : (P : NeTraces) → Σ Trace (_∈ traces P)
member (neTraces (t ∷ˡ _) _) = t , hereᴬ refl

-- and membership of a singleton pins it down

only-member : {s t : Trace} → s ∈ (t ∷ˡ []ˡ) → s ≡ t
only-member (hereᴬ p) = p

no-common-grade : (grade : E)
                → opTime send  ·ₑ uₑ ≾ₑ grade
                → opTime write ·ₑ uₑ ≾ₑ grade
                → ⊥
no-common-grade grade send-fits write-fits with member grade
... | t , t∈grade with only-member (∈-⊑ send-fits t∈grade)
...   | refl with only-member (∈-⊑ write-fits t∈grade)
...     | ()

-- the three grades one would reach for, refuted one at a time

storing-branch-at-the-transmission : ¬ (opTime write ·ₑ uₑ ≾ₑ ⟅ ⌈ send ⌉ ⟆)
storing-branch-at-the-transmission = fails

transmitting-branch-at-the-store : ¬ (opTime send ·ₑ uₑ ≾ₑ ⟅ ⌈ write ⌉ ⟆)
transmitting-branch-at-the-store = fails

neither-at-the-union : ¬ (opTime send ·ₑ uₑ ≾ₑ ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆)
neither-at-the-union = fails

-- what `if` can do here is branch over data: both branches make the
-- same run, so they are already at one grade

either-reading : [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ⟆
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

------------------------------------------------------------------------
-- Unboxing: a resource demanding exactly its run
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`, which here asks every run the
-- box demands to be one the computation exhibited. With both sides
-- singletons that is equality: the box names the run that has to have
-- happened, and nothing else will do.

demand : R
demand = ⟅ ⌈ read ⌉ ⟆

claim-after-sampling : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-sampling =
  box {ρ = demand} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
        (perform send here (return ⋆))))

handed-over : [] ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box {ρ = demand} (const 42)
    (lam (perform read ⋆
           (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
             (perform send here (return ⋆))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box {ρ = demand} (const 42)
    (perform read ⋆
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- doing more than the demanded run does not discharge it: the elapsed
-- run has to be the run the box names

storing-as-well : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ demand)
storing-as-well = fails

-- a second reading is not the one reading it demands either, though at
-- the coverage order of `Traces.Timed.LeftSided` it would be

two-readings-as-well : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime read ≾ᵣ demand)
two-readings-as-well = fails

idling-instead : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ demand)
idling-instead = fails

claiming-at-once : ¬ (uᵣ ≾ᵣ demand)
claiming-at-once = failsᵉ uᵣ demand

-- and a box demanding nothing but the empty run is the one claimable
-- at once

nothing-demanded : R
nothing-demanded = ⟅ ε ⟆

claiming-now : [] ⊢C⦂ Unit ‼ ⟅ ⌈ send ⌉ ⟆
claiming-now =
  box {ρ = nothing-demanded} (const 42)
    (unbox Hd (holdsᵉ uᵣ nothing-demanded)
      (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- `no-common-grade` settles this too, the resource grades being the
-- same monoid: a box claimed after a reading in one branch and after a
-- transmission in the other would have to demand both runs and neither.

sampling-branch-demands-its-run : uᵣ ·ᵣ opTime read ≾ᵣ ⟅ ⌈ read ⌉ ⟆
sampling-branch-demands-its-run = holds

transmitting-branch-cannot-meet-it : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ ⟅ ⌈ read ⌉ ⟆)
transmitting-branch-cannot-meet-it = fails

------------------------------------------------------------------------
-- Programs written at these demands
--
-- The box demands a reading and a store, which the run makes before
-- claiming it; the `if` afterwards chooses what to transmit and leaves
-- the grade alone.

logged : R
logged = ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆

log-then-claim :
  [] ∷ Bool ⊢C⦂ Unit ‼ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
log-then-claim =
  box {ρ = logged} (const 42)
    (perform read ⋆
      (perform write here
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) holds
          (if eternal-var Boolₑ
                (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))))
            `then perform send here (return ⋆)
            `else perform send (const 0) (return ⋆)))))

-- claiming it after the reading alone leaves the store undone

reading-alone : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ logged)
reading-alone = fails

-- and a transmission in its place is not the store it demands

transmitting-instead : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ logged)
transmitting-instead = fails

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ ⟅ ⌈ read ⌉ ⟆
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in (return here)

identified : Node ⊢C⦂ NodeId ‼ ⟅ ⌈ read ⌉ ⟆
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: its grade demands a run that
-- performs the operation, and returning at once makes the empty run

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = failsᵉ uₑ (op-grade read ·ₑ uₑ)
