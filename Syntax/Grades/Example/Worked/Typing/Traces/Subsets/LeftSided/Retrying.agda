------------------------------------------------------------------------
-- Where non-singleton grades come from at the conjunctive floor.      --
--                                                                     --
-- `Subsets.LeftSided` grades each operation by the single run that     --
-- performs it, and at that signature no program has a grade listing    --
-- two *different* runs: products of singletons are singletons,         --
-- `coerce` can only pad a list with copies of the run that happened,   --
-- and `no-common-listed-grade` closes the remaining door, `if`, at     --
-- every grade but `no-demand`, which lists nothing. The grade          --
-- looks degenerate as a result -- every `unbox` premise is an equality --
-- and every union is refused.                                         --
--                                                                     --
-- That is an artefact of the signature, not of the grade. A floor read --
-- conjunctively is about what a computation must be *able* to do, and  --
-- the natural way to demand several things is to grade one operation   --
-- with several runs. Here `send` is a transmitter that may retry: its  --
-- grade demands that a single transmission and a doubled one both be   --
-- available, and everything sequenced with it inherits both runs.      --
--                                                                     --
-- Everything else is as in `Subsets.LeftSided` -- the same language,   --
-- the same order -- so the two files differ only in `opTime`.          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Subsets.LeftSided.Retrying
  where

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; ε; _∙_; ⌈_⌉; ⟨_⟩; ⟅_⟆; ⟅_∣_⟆; ⟅_∣_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Subsets.LeftSided
  using (left-sided; Demands; demanding_; no-demand; holds; fails)

------------------------------------------------------------------------
-- The operations, with a transmitter that may retry
--
-- `read` and `write` do one thing each; `send` must be able to transmit
-- once and, should that fail, twice.

opTime : Op → Demands
opTime read  = demanding ⟅ ⌈ read ⌉ ⟆
opTime write = demanding ⟅ ⌈ write ⌉ ⟆
opTime send  = demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆

open import Syntax.Grades.Example.Worked.Typing.Core left-sided opTime

------------------------------------------------------------------------
-- Programs whose grades list two runs
--
-- A `perform` of the transmitter is graded by both runs it must have
-- available, and sequencing carries both through -- the language
-- product pairing each run of one grade with each run of the other.

transmitting :
  [] ∷ Reading ⊢C⦂ Unit ‼ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
transmitting =
  perform send here  -- ⟨ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
    (return ⋆)

relaying :
  [] ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
relaying =
  perform read ⋆  -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform send here  -- ⟨ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

-- a store is still graded by its one run, so the two families sit side
-- by side in the same language

storing : [] ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing =
  perform read ⋆  -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform write here  -- ⟨ demanding ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

------------------------------------------------------------------------
-- Sub-effecting between two-run grades
--
-- Weakening drops demands, and now there are two distinct demands to
-- drop: the transmitter may be retyped as guaranteeing the single
-- transmission alone, or the doubled one alone, and neither coercion is
-- reversible.

forgetting-the-retry : [] ∷ Reading ⊢C⦂ Unit ‼ demanding ⟅ ⌈ send ⌉ ⟆
forgetting-the-retry = coerce holds (perform send here (return ⋆))

keeping-only-the-retry :
  [] ∷ Reading ⊢C⦂ Unit ‼ demanding ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
keeping-only-the-retry = coerce holds (perform send here (return ⋆))

-- and a third run cannot be demanded of it: the transmitter is not
-- asked to be able to send three times

no-third-run :
  ¬ (opTime send ·ₑ uₑ
     ≾ₑ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
no-third-run = fails

------------------------------------------------------------------------
-- Unboxing against a two-run grade
--
-- `unbox`'s premise is `elapsed ≾ᵣ ρ`, which here asks `ρ ⊆ elapsed`.
-- With the transmitter's two runs elapsed, a box demanding either of
-- them is claimable -- and the inclusion is proper, so the premise is
-- not the equality it is forced into when every grade is a singleton.

claim-after-transmitting :
  [] ∷ Reading ⊢C⦂ Reading ‼ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-transmitting =
  box {ρ = demanding ⟅ ⌈ send ⌉ ⟆} (const 42)  -- ∷ [ demanding ⟅ ⌈ send ⌉ ⟆ ] Reading
    (perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
                  -- ⟨ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds -- ∷ Reading
        (return here)))

-- the box may demand the retry instead, which the same run discharges

retry-demanded : uᵣ ·ᵣ opTime send ≾ᵣ demanding ⟅ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
retry-demanded = holds

-- or both at once, which is where the premise becomes an equality
-- again -- the box asking for exactly what the operation guarantees

both-demanded :
  uᵣ ·ᵣ opTime send ≾ᵣ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
both-demanded = holds

-- what it may not demand is a run the transmitter does not have: a
-- reading, or a third transmission

reading-not-available : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ demanding ⟅ ⌈ read ⌉ ⟆)
reading-not-available = fails

third-send-not-available :
  ¬ (uᵣ ·ᵣ opTime send
     ≾ᵣ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
third-send-not-available = fails

-- after a reading as well, both runs carry the reading with them, and a
-- box demanding either of those is claimable

claim-after-relaying :
  [] ⊢C⦂ Reading ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-relaying =
  box {ρ = demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆} (const 42)
                  -- ∷ [ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ ] Reading
    (perform read ⋆  -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (perform send here  -- ⟨ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) holds
                  -- ∷ Reading
          (return here))))

-- and the transmitter's own runs are not, the reading having been
-- prefixed to them

bare-send-not-demanded :
  ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send
     ≾ᵣ demanding ⟅ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆)
bare-send-not-demanded = fails

------------------------------------------------------------------------
-- What has not changed
--
-- `if` still cannot join branches that do different things: a common
-- grade would have to be a non-empty subset of both branches' grades,
-- and a store's and a transmitter's have no run in common. Several runs
-- per grade is a property of an operation here, not something a
-- conditional can produce.

storing-branch-not-at-the-transmission :
  ¬ (opTime write ·ₑ uₑ ≾ₑ opTime send ·ₑ uₑ)
storing-branch-not-at-the-transmission = fails

transmitting-branch-not-at-the-store :
  ¬ (opTime send ·ₑ uₑ ≾ₑ opTime write ·ₑ uₑ)
transmitting-branch-not-at-the-store = fails
