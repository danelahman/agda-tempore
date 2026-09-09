------------------------------------------------------------------------
-- Typed example computations at the Egli-Milner grade.                --
--                                                                     --
-- A grade `[ P , Q ]` is read against the runs `X` a computation may   --
-- have as `P ⊆ X ⊆ Q`: every listed trace of `P` is a run it can       --
-- exhibit, and every run it has is listed in `Q`. The floor is read    --
-- conjunctively and the cap disjunctively, and the coherence field     --
-- asks `P ⊆ Q`, which is exactly what it takes for some run-set to sit --
-- between them.                                                       --
--                                                                     --
-- Against the calculus this behaves as its floor. A computation here   --
-- has one run, so `P ⊆ X` pins `P` to that run; coherence then puts it --
-- in `Q` already, and the cap never refuses a claim the floor allows.  --
-- Both consequences of the conjunctive floor carry over: `unbox` needs --
-- precisely the run the box names, and `no-common-grade` below shows   --
-- that no grade types a conditional whose branches perform different   --
-- operations. Branching over *data* is what is left, and it needs no   --
-- coercion at all.                                                     --
--                                                                     --
-- The comments inside the programs say what each former appends to the --
-- context its subcomputation is typed in: `⟨ ρ ⟩` a lock, `∷ A` a      --
-- binding. A grade with a name of its own is named there rather than   --
-- written out, these being pairs of trace sets.                        --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Subsets.TwoSided where

open import Data.Empty using (⊥)
open import Data.List.Base using () renaming (_∷_ to _∷ˡ_; [] to []ˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_;
         Trace; NeTraces; neTraces; traces; _∙_; ⌈_⌉; ⟨_⟩; ⟅_⟆; ⟅_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Subsets.TwoSided
  using (TwoSided; [_,_,_]; lo; two-sided; holds; fails; exact)

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ using (∈-⊑)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them, at both ends

opTime : Op → TwoSided
opTime o = exact ⌈ o ⌉

open import Syntax.Grades.Example.Worked.Typing.Core two-sided opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- A computation with one run is pinned exactly: its run is the only one
-- reachable and the only one permitted, and each lock is the one-event
-- pair of the operation that put it up.

sampling : [] ⊢C⦂ Reading ‼ exact ⌈ read ⌉
sampling =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ exact (⌈ read ⌉ ∙ ⌈ write ⌉)
storing =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (perform write here              -- ⟨ exact ⌈ write ⌉ ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ exact (⌈ read ⌉ ∙ ⌈ send ⌉)
relaying =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (perform send here               -- ⟨ exact ⌈ send ⌉ ⟩ ∷ Unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ exact (⌈ read ⌉ ∙ ⌈ send ⌉)
tagged-relaying =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = fails (uᵣ ·ᵣ opTime read) uᵣ

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ exact ⌈ read ⌉
carried-id =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- The two endpoints weaken in opposite directions, and from a run that
-- is pinned only the cap has anywhere to go: `coerce` may permit runs
-- the computation does not make, and may not drop the one it does.

permitting-more :
  [] ⊢C⦂ Unit ‼ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
                , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
permitting-more =
  coerce (holds _ _) (perform read ⋆ (perform write here (return ⋆)))

demanding-more :
  ¬ (opTime read ·ₑ (opTime write ·ₑ uₑ)
     ≾ₑ [ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
        , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ])
demanding-more = fails _ _

------------------------------------------------------------------------
-- Conditional branching
--
-- The floor refuses a common grade for branches that do different
-- things, exactly as at the one-sided floor.

member : (P : NeTraces) → Σ Trace (_∈ traces P)
member (neTraces (t ∷ˡ _) _) = t , hereᴬ refl

only-member : {s t : Trace} → s ∈ (t ∷ˡ []ˡ) → s ≡ t
only-member (hereᴬ p) = p

no-common-grade : (grade : E)
                → opTime send  ·ₑ uₑ ≾ₑ grade
                → opTime write ·ₑ uₑ ≾ₑ grade
                → ⊥
no-common-grade grade send-fits write-fits with member (lo grade)
... | t , t∈grade with only-member (∈-⊑ (proj₁ send-fits) t∈grade)
...   | refl with only-member (∈-⊑ (proj₁ write-fits) t∈grade)
...     | ()

-- branching over data instead: both branches make the same run, so
-- neither is coerced and neither locks the context

either-reading :
  [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ exact ⌈ send ⌉
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

------------------------------------------------------------------------
-- Unboxing: a resource demanding exactly its run
--
-- `unbox`'s premise asks the box's demanded runs to be among those the
-- computation exhibited and its own run to be permitted. The first pins
-- the elapsed run -- the product of the locks in between -- and
-- coherence then settles the second.

demand : R
demand = [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ , tt ]

claim-after-sampling : [] ⊢C⦂ Unit ‼ exact (⌈ read ⌉ ∙ ⌈ send ⌉)
claim-after-sampling =
  box {ρ = demand} (const 42)        -- ∷ [ demand ] Reading
    (perform read ⋆                  -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

handed-over : [] ⊢C⦂ Unit ‼ exact (⌈ read ⌉ ∙ ⌈ send ⌉)
handed-over =
  box {ρ = demand} (const 42)        -- ∷ [ demand ] Reading
    (lam                             -- ∷ [ demand ] Reading
       (perform read ⋆               -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _)
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ exact (⌈ read ⌉ ∙ ⌈ send ⌉)
either-way =
  box {ρ = demand} (const 42)        -- ∷ [ demand ] Reading
    (perform read ⋆                  -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _)
                                     -- ∷ Reading
        (if eternal-var Boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- storing as well makes a run the box permits, and it is still refused:
-- the run the box *demands* is then not one the computation has

storing-as-well : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ demand)
storing-as-well = fails (uᵣ ·ᵣ opTime read ·ᵣ opTime write) demand

idling-instead : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ demand)
idling-instead = fails (uᵣ ·ᵣ of-natʳ 2) demand

claiming-at-once : ¬ (uᵣ ≾ᵣ demand)
claiming-at-once = fails uᵣ demand

------------------------------------------------------------------------
-- Programs written at these intervals
--
-- The box demands a reading and a store; the run makes exactly that
-- before claiming it -- two locks multiplying to the demanded run --
-- and the `if` afterwards picks what to transmit without touching the
-- grade.

logged : R
logged = exact (⌈ read ⌉ ∙ ⌈ write ⌉)

log-then-claim :
  [] ∷ Bool ⊢C⦂ Unit ‼ exact (⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉)
log-then-claim =
  box {ρ = logged} (const 42)        -- ∷ [ logged ] Reading
    (perform read ⋆                  -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (perform write here            -- ⟨ exact ⌈ write ⌉ ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (holds _ _)
                                     -- ∷ Reading
          (if eternal-var Boolₑ
                (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))))
            `then perform send here (return ⋆)
            `else perform send (const 0) (return ⋆)))))

reading-alone : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ logged)
reading-alone = fails (uᵣ ·ᵣ opTime read) logged

transmitting-instead :
  ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ logged)
transmitting-instead = fails (uᵣ ·ᵣ opTime read ·ᵣ opTime send) logged

------------------------------------------------------------------------
-- Effect handling
--
-- Handling locks its `in` part by the handled computation's grade,
-- exactly as sequencing does.

forwarded : [] ⊢C⦂ Reading ‼ exact ⌈ read ⌉
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ exact ⌈ read ⌉
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = fails uₑ (op-grade read ·ₑ uₑ)
