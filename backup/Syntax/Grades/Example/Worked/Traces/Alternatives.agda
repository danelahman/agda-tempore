------------------------------------------------------------------------
-- What a grade offering alternatives says, across the whole grid.     --
--                                                                     --
-- Between singleton grades the three lifts agree, so nothing in the   --
-- lift axis is visible there and only the order axis is. This module  --
-- puts *non-singleton* sets through all six lifted grades at once --  --
-- three lifts against two sub-trace orders -- so that each scenario   --
-- reads as a table whose every entry is decided.                      --
--                                                                     --
-- The runs the scenarios are built from all take ten ticks under      --
-- `cost` -- read 1, write 3, send 6 -- and differ only in where the   --
-- write falls relative to the read and the send:                      --
--                                                                     --
--   ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉    between them                   --
--   ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉    before the read                --
--   ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉    after the send                 --
--                                                                     --
-- against the demand `⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉`, which asks for    --
-- two ticks between the two operations it names. Of the three, the    --
-- lenient order accepts the first two and the time-strict order only  --
-- the first, so a set built from them puts both axes in play.         --
--                                                                     --
-- Two readings are worth keeping apart while reading the tables.      --
--                                                                     --
--   * The lower (Hoare) lift asks each trace on one side to be        --
--     matched *somewhere* on the other -- an alternative may carry    --
--     the whole grade.                                                --
--   * The upper (Smyth) lift asks each trace on the *other* side to   --
--     be matched back -- every alternative must pull its weight.      --
--                                                                     --
-- So adding an alternative weakens a lower-lift claim and strengthens --
-- an upper-lift one, and the convex lift, being their conjunction,    --
-- fails as soon as either does.                                       --
--                                                                     --
-- `Inclusion` sees none of this: it asks a run to be listed literally, --
-- so it rejects every scenario below and is left out of the tables.   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Alternatives where

open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (¬_; Dec)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades.Example.Worked.Operations

------------------------------------------------------------------------
-- Closing a claim by running the grade's own decision procedure
--
-- Every grade below is decided, so one pair of helpers serves them all;
-- naming the procedure at the use site is what records which grade a
-- claim is about. They are stated at an arbitrary carrier so that the
-- set-level lifts, which the intervals' consistency fields are phrased
-- in, are covered too.

holds : {A : Set} {R : A → A → Set}
      → (R? : (x y : A) → Dec (R x y))
      → {x y : A} {p : True (R? x y)} → R x y
holds R? {p = p} = toWitness p

fails : {A : Set} {R : A → A → Set}
      → (R? : (x y : A) → Dec (R x y))
      → {x y : A} {p : False (R? x y)} → ¬ (R x y)
fails R? {p = p} = toWitnessFalse p

------------------------------------------------------------------------
-- Floors: what must have happened
--
-- `P ≾ Q` with `P` the runs that may have elapsed and `Q` the demands
-- on the box being opened. Reading the two lifts out at this row:
--
--   lower   every demand of `Q` is covered by some run of `P`
--   upper   every run of `P` covers some demand of `Q`

module Floors where

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡ_; _≾?_ to _≾ˡ?_)
  open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᵘ_; _≾?_ to _≾ᵘ?_)
  open import Syntax.Grades.Example.Traces.Subtrace.Convex.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶜ_; _≾?_ to _≾ᶜ?_)

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵗ_; _≾?_ to _≾ˡᵗ?_)
  open import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᵘᵗ_; _≾?_ to _≾ᵘᵗ?_)
  open import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶜᵗ_; _≾?_ to _≾ᶜᵗ?_)

  --------------------------------------------------------------------
  -- (A) The run logged in the window, or logged before the read
  --
  -- One alternative satisfies the demand under either order; the other
  -- satisfies it only leniently. So the lower lift, which needs one
  -- good alternative, is order-blind here, and the upper lift, which
  -- needs both, is exactly where the order shows.
  --
  --                  lower     upper     convex
  --   lenient        holds     holds     holds
  --   time-strict    holds     FAILS     FAILS

  A-lower : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
            ≾ˡ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  A-lower = holds _≾ˡ?_

  A-upper : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
            ≾ᵘ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  A-upper = holds _≾ᵘ?_

  A-convex : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
             ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  A-convex = holds _≾ᶜ?_

  A-lower-timed :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  A-lower-timed = holds _≾ˡᵗ?_

  A-upper-timed :
    ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
      ≾ᵘᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  A-upper-timed = fails _≾ᵘᵗ?_

  A-convex-timed :
    ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
      ≾ᶜᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  A-convex-timed = fails _≾ᶜᵗ?_

  --------------------------------------------------------------------
  -- (B) The run logged in the window, or logged after the send
  --
  -- The second alternative satisfies the demand under *neither* order,
  -- banking running forwards only. So this scenario separates the two
  -- lifts and says nothing about the orders -- the contrast with (A),
  -- where the same shape of set separates the orders as well.
  --
  --                  lower     upper     convex
  --   lenient        holds     FAILS     FAILS
  --   time-strict    holds     FAILS     FAILS

  B-lower : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
            ≾ˡ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  B-lower = holds _≾ˡ?_

  B-upper : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
              ≾ᵘ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  B-upper = fails _≾ᵘ?_

  B-convex : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
               ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  B-convex = fails _≾ᶜ?_

  B-lower-timed :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
    ≾ˡᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  B-lower-timed = holds _≾ˡᵗ?_

  B-upper-timed :
    ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
      ≾ᵘᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  B-upper-timed = fails _≾ᵘᵗ?_

  B-convex-timed :
    ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
      ≾ᶜᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  B-convex-timed = fails _≾ᶜᵗ?_

  --------------------------------------------------------------------
  -- (C) The run logged before the read, or after the send
  --
  -- Neither alternative logs in the window, so the *lower* lift -- the
  -- one that was order-blind in (A) -- turns on the order here: the
  -- only alternative that can carry the grade is the early one, and it
  -- carries it only leniently.
  --
  --                  lower     upper     convex
  --   lenient        holds     FAILS     FAILS
  --   time-strict    FAILS     FAILS     FAILS

  C-lower : ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
            ≾ˡ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  C-lower = holds _≾ˡ?_

  C-upper : ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
              ≾ᵘ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  C-upper = fails _≾ᵘ?_

  C-convex : ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
               ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  C-convex = fails _≾ᶜ?_

  C-lower-timed :
    ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
      ≾ˡᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  C-lower-timed = fails _≾ˡᵗ?_

  C-upper-timed :
    ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
      ≾ᵘᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  C-upper-timed = fails _≾ᵘᵗ?_

  C-convex-timed :
    ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
      ≾ᶜᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  C-convex-timed = fails _≾ᶜᵗ?_

  --------------------------------------------------------------------
  -- (D) Alternatives on the demand side, one of them unreachable
  --
  -- The set on the right now lists two demands. The lower lift asks
  -- both to be covered, and twenty ticks of idling is more than the
  -- ten the run takes; the upper lift asks only that the run cover one
  -- of them, which the read does. Neither reading consults the order,
  -- so this scenario isolates the lift axis on the demand side.
  --
  --                  lower     upper     convex
  --   lenient        FAILS     holds     FAILS
  --   time-strict    FAILS     holds     FAILS

  D-lower : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
              ≾ˡ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  D-lower = fails _≾ˡ?_

  D-upper : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ ≾ᵘ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
  D-upper = holds _≾ᵘ?_

  D-convex : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
               ≾ᶜ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  D-convex = fails _≾ᶜ?_

  D-lower-timed : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                    ≾ˡᵗ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  D-lower-timed = fails _≾ˡᵗ?_

  D-upper-timed : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆ ≾ᵘᵗ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
  D-upper-timed = holds _≾ᵘᵗ?_

  D-convex-timed : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                     ≾ᶜᵗ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  D-convex-timed = fails _≾ᶜᵗ?_

  --------------------------------------------------------------------
  -- (E) Repairing (A) by listing a weaker demand
  --
  -- What sank the time-strict upper lift in (A) was the early-logging
  -- alternative covering no listed demand. Offering a bare read as a
  -- second demand gives it one, and every entry becomes a `holds` --
  -- a grade offering alternatives is weakened on the demand side in
  -- exactly the way the upper lift needs.
  --
  --                  lower     upper     convex
  --   lenient        holds     holds     holds
  --   time-strict    holds     holds     holds

  E-lower : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
            ≾ˡ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  E-lower = holds _≾ˡ?_

  E-upper : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
            ≾ᵘ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  E-upper = holds _≾ᵘ?_

  E-convex : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
             ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  E-convex = holds _≾ᶜ?_

  E-lower-timed :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  E-lower-timed = holds _≾ˡᵗ?_

  E-upper-timed :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ᵘᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  E-upper-timed = holds _≾ᵘᵗ?_

  E-convex-timed :
    ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ᶜᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  E-convex-timed = holds _≾ᶜᵗ?_

------------------------------------------------------------------------
-- Caps: what may have happened
--
-- `P ≾ Q` with `P` still the runs that may have elapsed and `Q` now the
-- permissions. The two lifts swap roles against the floors above:
--
--   lower   every run of `P` stays within some allowance of `Q`
--   upper   every allowance of `Q` is realised by some run of `P`

module Caps where

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡ_; _≾?_ to _≾ˡ?_)
  open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᵘ_; _≾?_ to _≾ᵘ?_)
  open import Syntax.Grades.Example.Traces.Subtrace.Convex.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶜ_; _≾?_ to _≾ᶜ?_)

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵗ_; _≾?_ to _≾ˡᵗ?_)
  open import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᵘᵗ_; _≾?_ to _≾ᵘᵗ?_)
  open import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶜᵗ_; _≾?_ to _≾ᶜᵗ?_)

  --------------------------------------------------------------------
  -- (F) A cap offering both placements of the write
  --
  -- The mirror of (A). The lower lift needs the uplink schedule to fit
  -- inside one of the two allowances, which the in-window one supplies
  -- under either order; the upper lift needs both allowances to be
  -- realised, and the early one is realisable only leniently.
  --
  --                  lower     upper     convex
  --   lenient        holds     holds     holds
  --   time-strict    holds     FAILS     FAILS

  F-lower : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
            ≾ˡ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  F-lower = holds _≾ˡ?_

  F-upper : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
            ≾ᵘ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  F-upper = holds _≾ᵘ?_

  F-convex : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
             ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  F-convex = holds _≾ᶜ?_

  F-lower-timed :
    ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵗ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  F-lower-timed = holds _≾ˡᵗ?_

  F-upper-timed :
    ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
      ≾ᵘᵗ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  F-upper-timed = fails _≾ᵘᵗ?_

  F-convex-timed :
    ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
      ≾ᶜᵗ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  F-convex-timed = fails _≾ᶜᵗ?_

  --------------------------------------------------------------------
  -- (G) A run that might have exceeded the cap
  --
  -- Alternatives on the elapsed side now, against a single allowance.
  -- The lower lift asks every possible run to stay within it, and the
  -- second does not; the upper lift asks only that the allowance be
  -- realised, which the first run does. Neither reading consults the
  -- order, so the lift axis is again isolated.
  --
  --                  lower     upper     convex
  --   lenient        FAILS     holds     FAILS
  --   time-strict    FAILS     holds     FAILS

  G-lower : ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
              ≾ˡ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆)
  G-lower = fails _≾ˡ?_

  G-upper : ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
            ≾ᵘ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  G-upper = holds _≾ᵘ?_

  G-convex : ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
               ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆)
  G-convex = fails _≾ᶜ?_

  G-lower-timed : ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
                    ≾ˡᵗ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆)
  G-lower-timed = fails _≾ˡᵗ?_

  G-upper-timed : ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
                  ≾ᵘᵗ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  G-upper-timed = holds _≾ᵘᵗ?_

  G-convex-timed : ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
                     ≾ᶜᵗ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆)
  G-convex-timed = fails _≾ᶜᵗ?_

  --------------------------------------------------------------------
  -- (H) Two possible runs against two allowances, matched crosswise
  --
  -- Both sides list alternatives, and leniently they match crosswise:
  -- each run stays within one of the allowances, and each allowance is
  -- realised by one of the runs.
  --
  -- Under the time-strict order the uplink schedule no longer sits
  -- inside the early-logging allowance, and the two lifts part company
  -- over what that costs. The lower lift fails: that run is left with
  -- nothing to fit inside, the bare read being far too small. The upper
  -- lift survives, because it needs only *some* run to realise the
  -- early-logging allowance, and the bare read still does -- a demand
  -- naming no delay never feels the window discipline. So the convex
  -- lift fails through its Hoare half alone.
  --
  -- This is (F) the other way round: there the order change cost the
  -- upper lift and spared the lower one.
  --
  --                  lower     upper     convex
  --   lenient        holds     holds     holds
  --   time-strict    FAILS     holds     FAILS

  H-lower : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
            ≾ˡ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  H-lower = holds _≾ˡ?_

  H-upper : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
            ≾ᵘ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  H-upper = holds _≾ᵘ?_

  H-convex : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
             ≾ᶜ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  H-convex = holds _≾ᶜ?_

  H-lower-timed : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
                    ≾ˡᵗ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆)
  H-lower-timed = fails _≾ˡᵗ?_

  H-upper-timed : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
                  ≾ᵘᵗ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
  H-upper-timed = holds _≾ᵘᵗ?_

  H-convex-timed : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆
                     ≾ᶜᵗ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ⟆)
  H-convex-timed = fails _≾ᶜᵗ?_

------------------------------------------------------------------------
-- Intervals: alternatives at both endpoints
--
-- A two-sided grade pairs a floor with a cap, and its consistency field
-- asks the floor to sit inside the cap. With alternatives at either
-- endpoint that field is itself a lift, so it can be lost when the
-- order tightens: a pair of sets that *is* an interval over the lenient
-- order need not be one over the time-strict order at all.

module Intervals where

  open import Data.Unit using (tt)

  open import Syntax.Grades.Traces.Sets Op using (traces)

  open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost
    using (_≼ˢ_; _≼ˢ?_)
  open import Syntax.Grades.Traces.SubtraceTimedLift Op _≟ₒ_ cost
    using () renaming (_≼ˢ_ to _≼ˢᵗ_; _≼ˢ?_ to _≼ˢᵗ?_)

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.TwoSided
    Op _≟ₒ_ cost using (TraceInterval; [_,_,_]; _≾ᵗⁱ_; _≾ᵗⁱ?_)

  -- the intervals are taken explicitly here: the decision has to be run
  -- on known endpoints before the `True` witness can be filled in

  holdsⁱ : (i j : TraceInterval) {p : True (i ≾ᵗⁱ? j)} → i ≾ᵗⁱ j
  holdsⁱ i j {p} = toWitness p

  failsⁱ : (i j : TraceInterval) {p : False (i ≾ᵗⁱ? j)} → ¬ (i ≾ᵗⁱ j)
  failsⁱ i j {p} = toWitnessFalse p

  --------------------------------------------------------------------
  -- A cap listing two placements of the write, neither in the window
  --
  -- The floor is the uplink schedule and the cap offers logging before
  -- the read or after the send. Leniently the first of those is above
  -- the floor, so the pair is an interval; time-strictly neither is,
  -- and the consistency field cannot be filled.

  consistent-leniently :
    traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    ≼ˢ traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  consistent-leniently = holds _≼ˢ?_

  inconsistent-time-strictly :
    ¬ (traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
      ≼ˢᵗ traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆)
  inconsistent-time-strictly = fails _≼ˢᵗ?_

  -- so the pair is a grade over the lenient order

  logged-outside-the-window : TraceInterval
  logged-outside-the-window =
    [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
    , consistent-leniently
    ]

  --------------------------------------------------------------------
  -- An interval both orders admit
  --
  -- Widening the cap with the in-window placement restores consistency
  -- under either order, the floor now having something above it that
  -- respects where the demanded time falls.

  consistent-either-way :
    traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    ≼ˢᵗ traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  consistent-either-way = holds _≼ˢᵗ?_

  --------------------------------------------------------------------
  -- Weakening an interval moves its endpoints in opposite directions
  --
  -- Both endpoints list alternatives here. Dropping a demand from the
  -- floor and adding an allowance to the cap weakens the grade; doing
  -- either in the other direction does not.

  polled-at-most-logged : TraceInterval
  polled-at-most-logged =
    [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
    , holds _≼ˢ?_
    ]

  polled-at-most-logged-or-early : TraceInterval
  polled-at-most-logged-or-early =
    [ ⟅ ⌈ read ⌉ ⟆
    , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    , holds _≼ˢ?_
    ]

  weakened : polled-at-most-logged ≾ᵗⁱ polled-at-most-logged-or-early
  weakened = holdsⁱ polled-at-most-logged polled-at-most-logged-or-early

  not-the-other-way : ¬ (polled-at-most-logged-or-early ≾ᵗⁱ polled-at-most-logged)
  not-the-other-way = failsⁱ polled-at-most-logged-or-early polled-at-most-logged
