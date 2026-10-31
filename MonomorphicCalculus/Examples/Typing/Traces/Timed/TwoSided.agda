------------------------------------------------------------------------
-- Typed example computations at the grade of trace contracts.        --
--                                                                    --
-- A grade `[ P , Q ]` pairs a coverage floor with an allowance cap:  --
-- whatever the computation did, it covered one of the guarantees in  --
-- `P` and stayed within one of the allowances in `Q`. Each operation --
-- is graded by the one-event run that performs it, at both           --
-- endpoints.                                                         --
--                                                                    --
-- This is the trace counterpart of the two-sided time windows, the   --
-- two endpoints refusing independently, over the operations          --
-- performed rather than their duration. A box demands that certain   --
-- operations have been performed and that no more than its           --
-- allowance has been spent since, so a claim can be refused for      --
-- doing too little and for doing too much; the examples below        --
-- exhibit both.                                                      --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. A grade with a name is written by that name, the  --
-- grades being pairs of trace sets.                                  --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Traces.Timed.TwoSided where


open import Relation.Nullary using (¬_)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; _∙_; ⌈_⌉; ⟨_⟩)

open import Grades.Examples.Worked.Traces.Timed.TwoSided
  using (TwoSided; [_,_]; within_; unbounded; two-sided; holds; fails;
         exact; ⟅_⟆ˡᵒ; ⟅_∣_⟆ˡᵒ; ⟅_⟆; ⟅_∣_⟆)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them, at both ends

opTime : Op → TwoSided
opTime o = exact ⌈ o ⌉

open import MonomorphicCalculus.Examples.Typing.Core two-sided opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- A computation with one run is pinned exactly: its run is both the
-- guarantee it meets and the allowance it stays within, and each lock
-- is the one-event interval of the operation that put it up.

sampling : [] ⊢C⦂ Reading ! exact ⌈ read ⌉
sampling =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ unit ! exact (⌈ read ⌉ ∙ ⌈ write ⌉)
storing =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (perform write here              -- ⟨ exact ⌈ write ⌉ ⟩ ∷ unit
      (return ⋆))

relaying : [] ⊢C⦂ unit ! exact (⌈ read ⌉ ∙ ⌈ send ⌉)
relaying =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (perform send here               -- ⟨ exact ⌈ send ⌉ ⟩ ∷ unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ unit ! exact (⌈ read ⌉ ∙ ⌈ send ⌉)
tagged-relaying =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                                     -- ∷ NodeId ∷ Reading
      `with perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ 𝟏ᵣ` asks the cap to permit nothing but the empty run, which is
-- the upper endpoint deciding it, as at the two-sided windows. So no
-- lock but the unit may stand over a reading in use.

reading-stale-after-an-operation : ¬ (𝟏ᵣ ·ᵣ opTime read ≾ᵣ 𝟏ᵣ)
reading-stale-after-an-operation = fails (𝟏ᵣ ·ᵣ opTime read) 𝟏ᵣ

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ! exact ⌈ read ⌉
carried-id =
  perform read ⋆                     -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` weakens both endpoints at once, in opposite directions: the
-- guarantee may be forgotten down and the allowance relaxed up. The
-- context is untouched.

contract : E
contract = [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ ]

meeting-the-contract : [] ⊢C⦂ unit ! contract
meeting-the-contract =
  coerce (holds _ _) (perform read ⋆ (perform write here (return ⋆)))

-- the floor refuses a run that takes no reading, and the cap a run that
-- spends more than the allowance, each with the other endpoint met

idling-fails-the-floor : ¬ (ιₑ 5 ·ₑ 𝟏ₑ ≾ₑ contract)
idling-fails-the-floor = fails _ _

transmitting-twice-fails-the-cap :
  ¬ (opTime read ·ₑ (opTime send ·ₑ (opTime read ·ₑ 𝟏ₑ)) ≾ₑ contract)
transmitting-twice-fails-the-cap = fails _ _

------------------------------------------------------------------------
-- Conditional branching
--
-- Both branches are coerced to one contract, so its floor is what both
-- guarantee and its cap what neither exceeds. Two ticks and six do for
-- a store against a transmission: the store is certain of two and may
-- run to three.

window : E
window = [ ⟅ ⟨ 2 ⟩ ⟆ˡᵒ , within ⟅ ⟨ 6 ⟩ ⟆ ]

branching : [] ∷ bool ∷ Reading ⊢C⦂ unit ! window
branching =
  if eternal-var boolₑ (Tl-∷ Hd)
    `then coerce (holds _ _) (perform send  here (return ⋆))
    `else coerce (holds _ _) (perform write here (return ⋆))

-- three ticks are more than the storing branch guarantees, being the
-- store's worst case rather than its best

three-ticks-not-guaranteed :
  ¬ (opTime write ·ₑ 𝟏ₑ ≾ₑ [ ⟅ ⟨ 3 ⟩ ⟆ˡᵒ , within ⟅ ⟨ 6 ⟩ ⟆ ])
three-ticks-not-guaranteed = fails _ _

-- an `if` over data alone needs no contract found for it

either-reading :
  [] ∷ bool ∷ Reading ∷ Reading ⊢C⦂ unit ! exact ⌈ send ⌉
either-reading =
  if eternal-var boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

------------------------------------------------------------------------
-- Unboxing: a resource with a contract
--
-- `unbox`'s premise asks what elapsed (the product of the locks
-- between the box's binding and the claim) to cover the box's
-- guarantee and stay within its allowance. The box below asks for a
-- reading, and allows a reading and six ticks' worth of other work.

-- the run stores the reading as well before claiming, so neither
-- endpoint is met exactly: it covers the demanded reading with the
-- store left over, and spends three of the six the allowance leaves

claim-after-storing :
  [] ⊢C⦂ unit ! exact (⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉)
claim-after-storing =
  box contract (const reading 42)    -- ∷ [ contract ] Reading
    (perform read ⋆                  -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (perform write here            -- ⟨ exact ⌈ write ⌉ ⟩ ∷ unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

handed-over : [] ⊢C⦂ unit ! exact (⌈ read ⌉ ∙ ⌈ send ⌉)
handed-over =
  box contract (const reading 42)    -- ∷ [ contract ] Reading
    (fun                             -- ∷ [ contract ] Reading
       (perform read ⋆               -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

either-way : [] ∷ bool ⊢C⦂ unit ! exact (⌈ read ⌉ ∙ ⌈ send ⌉)
either-way =
  box contract (const reading 42)    -- ∷ [ contract ] Reading
    (perform read ⋆                  -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
        (if eternal-var boolₑ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))
          `then perform send here (return ⋆)
          `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆))))

-- too little: idling covers no reading, though it is well inside the
-- allowance

idling-covers-nothing : ¬ (𝟏ᵣ ·ᵣ ιᵣ 2 ≾ᵣ contract)
idling-covers-nothing = fails _ _

claiming-at-once : ¬ (𝟏ᵣ ≾ᵣ contract)
claiming-at-once = fails _ _

-- too much: a reading, a transmission and a reading take seven ticks
-- beyond the named reading, and the allowance is six

overspending :
  ¬ (𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime send ·ᵣ opTime read ≾ᵣ contract)
overspending = fails _ _

-- between the two, a store fits: it covers the reading and its three
-- ticks come out of the six

storing-fits : 𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ contract
storing-fits = holds _ _

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- A box whose guarantee lists both branches' runs and whose allowance
-- covers the costlier of them is within both branches' reach.

alternatives : R
alternatives = [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ˡᵒ , within ⟅ ⟨ 6 ⟩ ⟆ ]

claimed-in-both-branches :
  [] ⊢C⦂ unit ! [ ⟅ ⌈ send ⌉ ⟆ˡᵒ , within ⟅ ⟨ 12 ⟩ ⟆ ]
claimed-in-both-branches =
  box alternatives (const reading 42)        -- ∷ [ alternatives ] Reading
    (if true
      `then coerce (holds _ _)
              (perform read ⋆        -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce (holds _ _)
              (perform send (const reading 0)
                                     -- ⟨ exact ⌈ send ⌉ ⟩ ∷ unit
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆)))))

-- dropping the transmission from the guarantee closes that branch,
-- and tightening the allowance to a single tick closes it too

transmitting-branch-covers-nothing :
  ¬ (𝟏ᵣ ·ᵣ opTime send ≾ᵣ [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⟨ 6 ⟩ ⟆ ])
transmitting-branch-covers-nothing = fails _ _

transmitting-branch-overspends :
  ¬ (𝟏ᵣ ·ᵣ opTime send
     ≾ᵣ [ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ˡᵒ , within ⟅ ⟨ 1 ⟩ ⟆ ])
transmitting-branch-overspends = fails _ _

------------------------------------------------------------------------
-- Non-singleton grades at both endpoints
--
-- `if` joins its branches by taking the union at each endpoint, so a
-- conditional's grade lists what each branch does on both sides. The
-- box's floor is then met member by member (the sampling branch
-- covers the demanded reading, the storing branch the two ticks),
-- while its six ticks of allowance cover both branches at once.

branch-join : E
branch-join =
  [ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ]

mixed-contract : R
mixed-contract = [ ⟅ ⌈ read ⌉ ∣ ⟨ 2 ⟩ ⟆ˡᵒ , within ⟅ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ⟆ ]

sampling-branch-joins : opTime read ·ₑ 𝟏ₑ ≾ₑ branch-join
sampling-branch-joins = holds _ _

storing-branch-joins : opTime write ·ₑ 𝟏ₑ ≾ₑ branch-join
storing-branch-joins = holds _ _

claim-after-a-branch :
  [] ∷ bool ⊢C⦂ unit ! [ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ˡᵒ
                       , within ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ ]
claim-after-a-branch =
  box mixed-contract (const reading 42)
                                     -- ∷ [ mixed-contract ] Reading
    ((if eternal-var boolₑ (Tl-∷ Hd)
        `then coerce {ε' = branch-join} (holds _ _)
                (perform read ⋆ (return ⋆))
        `else coerce (holds _ _) (perform write (const reading 0) (return ⋆)))
      ⨟                              -- ⟨ branch-join ⟩ ∷ unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Programs written at these contracts
--
-- The contract claimed on both sides of an `if`: one branch takes the
-- reading it asks for, the other takes the reading and stores it,
-- spending three of the six the allowance leaves. Both then transmit,
-- so the conditional keeps the reading as its guarantee and needs nine
-- ticks of allowance for the slower branch.

store-or-not :
  [] ∷ bool ⊢C⦂ unit ! [ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 9 ⟩ ⟆ ]
store-or-not =
  box contract (const reading 42)            -- ∷ [ contract ] Reading
    (if eternal-var boolₑ (Tl-∷ Hd)
      `then coerce (holds _ _)
              (perform read ⋆        -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
                (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
                  (perform send here (return ⋆))))
      `else coerce (holds _ _)
              (perform read ⋆        -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
                (perform write here  -- ⟨ exact ⌈ write ⌉ ⟩ ∷ unit
                  (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (holds _ _) (<:ᵛ-refl _)
                                     -- ∷ Reading
                    (perform send here (return ⋆))))))

-- the storing branch has to claim before it transmits: a store and a
-- transmission spend nine of an allowance that leaves six

storing-then-transmitting-first :
  ¬ (𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime write ·ᵣ opTime send ≾ᵣ contract)
storing-then-transmitting-first =
  fails (𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime write ·ᵣ opTime send) contract

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ! exact ⌈ read ⌉
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ! exact ⌈ read ⌉
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ exact ⌈ read ⌉ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: the floor asks for the
-- operation, and returning at once covers nothing

no-discarding : ¬ (𝟏ₑ ≾ₑ op-grade read ·ₑ 𝟏ₑ)
no-discarding = fails 𝟏ₑ (op-grade read ·ₑ 𝟏ₑ)
