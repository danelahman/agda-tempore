------------------------------------------------------------------------
-- Typed example computations at lower bounds on time paired with a   --
-- security level.                                                    --
--                                                                    --
-- Effect grades and resource grades are both `([ n ,+∞⟩ , ℓ)`, "at   --
-- least `n` time steps, touching nothing above `ℓ`", and an          --
-- operation is graded by the time it is guaranteed to take and the   --
-- level it touches: read 1 and write 2 at `Low`, send 4 at `High`.   --
--                                                                    --
-- Sequencing adds the times and joins the levels, so the level is a  --
-- floating label: once a run has transmitted, it is `High`           --
-- thereafter. As a resource grade, `[ ([ n ,+∞⟩ , Low) ] A` is an    --
-- embargoed report: the premise of `unbox` requires that `n` steps   --
-- have passed since boxing and that nothing since has touched        --
-- `High`. A claim can be refused for being early or for being        --
-- tainted; waiting removes the first reason and never the second.    --
-- Both refusals are shown below.                                     --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order   --
-- are decided by different components:                               --
--                                                                    --
--   * the bound `ρ ≾ᵣ uᵣ` of `var` holds exactly when `ρ` is `Low`:  --
--     time never makes a reading stale, and a transmission does.     --
--                                                                    --
--   * a handler clause cannot discard its continuation, returning at --
--     once guaranteeing none of the time of the operation.           --
--                                                                    --
-- Every claim is checked componentwise, `≤!` on the time and `⊑!` on --
-- the level; a refutation names the component that fails.            --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding.                                                   --
------------------------------------------------------------------------

module ClosedCalculus.Examples.Typing.Product.LeftSidedTimeLevel where

open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Examples.Time.LeftSided using (𝕀; [_,+∞⟩)
open import Grades.Examples.SecurityLevel
  using (LevelLattice; LowHigh; Low; High; _⊑ₗₕ_; low-high)
open import Grades.Examples.Product.LeftSidedTimeLevel
  using (left-sided-time×low-high)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; fast)
open import Grades.Examples.Worked.Operations.Footprint using (touches)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

open LevelLattice low-high using (_⊑?_)

-- the level component, decided by the lattice's own procedure

⊑! : {ℓ ℓ' : LowHigh} {p : True (ℓ ⊑? ℓ')} → ℓ ⊑ₗₕ ℓ'
⊑! {p = p} = toWitness p

⋢! : {ℓ ℓ' : LowHigh} {p : False (ℓ ⊑? ℓ')} → ¬ (ℓ ⊑ₗₕ ℓ')
⋢! {p = p} = toWitnessFalse p

------------------------------------------------------------------------
-- The operations, graded by guaranteed time and the level touched

open import Grades.Examples.Worked.Operations.Grading using (module Product-LeftSidedTimeLevel)
open Product-LeftSidedTimeLevel using (opTime) public

open import ClosedCalculus.Examples.Typing.Core
  left-sided-time×low-high opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- A computation's grade adds up the guaranteed times along it and
-- joins the levels: transmitting raises the label of the whole run.

sampling : [] ⊢C⦂ Reading ‼ ([ 1 ,+∞⟩ , Low)
sampling =
  perform read ⋆                     -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ ([ 3 ,+∞⟩ , Low)
storing =
  perform read ⋆                     -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
    (perform write here              -- ⟨ ([ 2 ,+∞⟩ , Low) ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ ([ 5 ,+∞⟩ , High)
relaying =
  perform read ⋆                     -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
    (perform send here               -- ⟨ ([ 4 ,+∞⟩ , High) ⟩ ∷ Unit
      (return ⋆))

------------------------------------------------------------------------
-- Readings survive time, not a transmission
--
-- `var` asks for `ρ ≾ᵣ uᵣ` at a non-eternal type. The time component
-- always meets it, the unit being the greatest floor; the level
-- component meets it only at `Low`.

-- the `logged-uplink` run: the reading is stored, and transmitted after
-- the store and two ticks of idling, all of them `Low`

logged-uplink : [] ⊢C⦂ Unit ‼ ([ 9 ,+∞⟩ , High)
logged-uplink =
  perform read ⋆                     -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
    (perform write here              -- ⟨ ([ 2 ,+∞⟩ , Low) ⟩ ∷ Unit
      (delay 2                       -- ⟨ ([ 2 ,+∞⟩ , Low) ⟩
        (perform send (fresh-var (≤! , ⊑!) (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))
                                     -- ⟨ ([ 4 ,+∞⟩ , High) ⟩ ∷ Unit
          (return ⋆))))

-- transmitting first and storing the reading afterwards is refused:
-- the reading would be used past a `High` lock

stale-after-transmitting : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ uᵣ)
stale-after-transmitting (_ , tainted) = ⋢! tainted

-- the identifier is eternal, and crosses a transmission all the same

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ ([ 4 ,+∞⟩ , High)
carried-id =
  perform send (const 0)             -- ⟨ ([ 4 ,+∞⟩ , High) ⟩ ∷ Unit
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- `coerce` forgets time and raises the level. Neither is reversible:
-- there is no declassifying a run that has transmitted.

raising-the-level : [] ⊢C⦂ Unit ‼ ([ 3 ,+∞⟩ , High)
raising-the-level =
  coerce (≤! , ⊑!) (perform read ⋆ (perform write here (return ⋆)))

no-declassifying : ¬ (opTime read ·ₑ (opTime send ·ₑ uₑ) ≾ₑ ([ 5 ,+∞⟩ , Low))
no-declassifying (_ , tainted) = ⋢! tainted

------------------------------------------------------------------------
-- Conditional branching
--
-- The join keeps the smaller floor and the higher level: a conditional
-- is `High` if either branch is.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ([ 2 ,+∞⟩ , High)
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce (≤! , ⊑!) (perform send  here (return ⋆))
    `else coerce (≤! , ⊑!) (perform write here (return ⋆))

-- the storing branch alone would have stayed `Low`

storing-is-low : opTime write ·ₑ uₑ ≾ₑ ([ 2 ,+∞⟩ , Low)
storing-is-low = ≤! , ⊑!

------------------------------------------------------------------------
-- Unboxing: an embargoed report
--
-- The report may be published once five steps have passed since it was
-- boxed, and only by code that has not transmitted in the meantime.

report : R
report = ([ 5 ,+∞⟩ , Low)

-- published after reading, storing and idling two ticks: five steps,
-- all `Low`

published : [] ⊢C⦂ Unit ‼ ([ 9 ,+∞⟩ , High)
published =
  box report (const 42)              -- ∷ [ report ] Reading
    (perform read ⋆                  -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
      (perform write here            -- ⟨ ([ 2 ,+∞⟩ , Low) ⟩ ∷ Unit
        (delay 2                     -- ⟨ ([ 2 ,+∞⟩ , Low) ⟩
          (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))) (≤! , ⊑!)
                 (<:ᵛ-refl _)        -- ∷ Reading
            (perform send here (return ⋆))))))

-- or after waiting the embargo out

waited-out : [] ⊢C⦂ Unit ‼ ([ 9 ,+∞⟩ , High)
waited-out =
  box report (const 42)              -- ∷ [ report ] Reading
    (delay 5                         -- ⟨ ([ 5 ,+∞⟩ , Low) ⟩
      (unbox (Tl-⟨⟩ Hd) (≤! , ⊑!) (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- read and stored only, it is still under embargo: three steps of five

too-early : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ report)
too-early (not-yet , _) = ≰! not-yet

-- relayed, the run is late enough and tainted

tainted : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ report)
tainted (_ , high) = ⋢! high

-- and waiting afterwards does not clean it

waiting-does-not-clean : ¬ (uᵣ ·ᵣ opTime send ·ᵣ of-durʳ 10 ≾ᵣ report)
waiting-does-not-clean (_ , high) = ⋢! high

-- a report cleared for the network may be published after a
-- transmission, the box's level being the ceiling on what came since

cleared : R
cleared = ([ 5 ,+∞⟩ , High)

relayed-then-published : [] ⊢C⦂ Unit ‼ ([ 9 ,+∞⟩ , High)
relayed-then-published =
  box cleared (const 42)             -- ∷ [ cleared ] Reading
    (perform read ⋆                  -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
      (perform send here             -- ⟨ ([ 4 ,+∞⟩ , High) ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ⊑!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

------------------------------------------------------------------------
-- Unboxing under a branch, and after one
--
-- Each branch discharges the premise at what it has itself done: the
-- quiet branch publishes, the transmitting branch does not try.

quiet-branch : [] ∷ Bool ⊢C⦂ Unit ‼ ([ 4 ,+∞⟩ , High)
quiet-branch =
  box report (const 42)              -- ∷ [ report ] Reading
    (if eternal-var Boolₑ (Tl-∷ Hd)
      `then coerce (≤! , ⊑!)
              (perform write (const 0)
                                     -- ⟨ ([ 2 ,+∞⟩ , Low) ⟩ ∷ Unit
                (delay 3             -- ⟨ ([ 3 ,+∞⟩ , Low) ⟩
                  (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) (≤! , ⊑!) (<:ᵛ-refl _)
                                     -- ∷ Reading
                    (perform send here (return ⋆)))))
      `else perform send (const 0) (return ⋆))

-- sequenced after a conditional, a claim is weighed against the join.
-- Two quiet branches keep it `Low`, and the report is published.

after-a-quiet-branch : [] ∷ Bool ⊢C⦂ Unit ‼ ([ 9 ,+∞⟩ , High)
after-a-quiet-branch =
  box report (const 42)              -- ∷ [ report ] Reading
    ((if eternal-var Boolₑ (Tl-∷ Hd)
        `then perform write (const 0) (delay 3 (return ⋆))
        `else delay 5 (return ⋆))
      ⨟                              -- ⟨ ([ 5 ,+∞⟩ , Low) ⟩ ∷ Unit
        unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≤! , ⊑!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))

-- with a transmitting branch instead of the idling one, the join is
-- `High`, and the claim is refused on either path

after-a-transmitting-branch : ¬ (uᵣ ·ᵣ ([ 4 ,+∞⟩ , High) ≾ᵣ report)
after-a-transmitting-branch (_ , high) = ⋢! high

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ ([ 1 ,+∞⟩ , Low)
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ ([ 1 ,+∞⟩ , Low)
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                              -- ⟨ ([ 1 ,+∞⟩ , Low) ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: a `return` guarantees none of
-- the operation's time

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding (early , _) = ≰! early

-- and none may close over a reading: the barrier `⊤ᵣ` is `High`

no-reporting : (op : Op) → (ε'' : E)
             → ¬ (uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ uᵣ)
no-reporting op ε'' (_ , ())
