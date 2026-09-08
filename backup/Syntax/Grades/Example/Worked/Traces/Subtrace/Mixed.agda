------------------------------------------------------------------------
-- Worked instances of the mixed column.                               --
--                                                                     --
-- `Grades.Example.Traces.Subtrace.Mixed`: a Smyth floor under a Hoare --
-- cap, the one pairing whose two endpoints both speak about every run  --
-- of a computation --                                                 --
--                                                                     --
--   floor   every run covers some listed demand                       --
--   cap     every run stays within some listed allowance              --
--                                                                     --
-- so a grade reads as a contract, and the runs meeting it are those    --
-- lying between its two endpoints. Weakening *adds* members at either  --
-- end: both sets are read disjunctively, so a longer list asks less.   --
--                                                                     --
-- Two sections read the order the way the typing rules do: as an       --
-- effect grade, where `coerce` moves along it, and as a resource       --
-- grade, where `unbox` discharges its premise against it.              --
--                                                                     --
-- Every run is written out in full in every claim, rather than through --
-- the shorthands of `Worked.Operations`, so that a claim can be read   --
-- without looking anything up. Under `cost` -- read 1, write 3, send   --
-- 6 -- the runs used below take                                        --
--                                                                     --
--   ⌈ read ⌉                                              1 tick      --
--   ⌈ read ⌉ ∙ ⟨ 1 ⟩                                      2 ticks     --
--   ⌈ write ⌉ ∙ ⟨ 1 ⟩                                     4 ticks     --
--   ⌈ write ⌉ ∙ ⌈ read ⌉                                  4 ticks     --
--   ⌈ read ⌉ ∙ ⌈ send ⌉ ,  ⌈ send ⌉ ∙ ⌈ read ⌉            7 ticks     --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ,  ⟨ 9 ⟩ ,  ⌈ write ⌉ ∙ ⌈ send ⌉      --
--                                                          9 ticks     --
--   ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉                      10 ticks     --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉               15 ticks     --
--                                                                     --
-- Every claim is closed by running the grade's own decision procedure, --
-- so one asserted the wrong way round does not typecheck, and the      --
-- consistency fields are `tt`: being `True`-of-a-decision, they are    --
-- discharged by computation on written-out endpoints.                  --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Subtrace.Mixed where

open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.Subtrace.Mixed.TwoSided Op _≟ₒ_ cost
  using (MixedInterval; [_,_,_]; lo; hi; _·ᵐⁱ_; _◇ˢ_; mixed-two-sided;
         _≾ᵐⁱ_; _≾ᵐⁱ?_) public

-- the two endpoints read one-sidedly, and the lifts the mixed column
-- does *not* use at each end, for the contrasts in the last section

open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.LeftSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶠ_; _≾?_ to _≾ᶠ?_)
open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.RightSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ᶜ_; _≾?_ to _≾ᶜ?_)
open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.LeftSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ʰᶠ_; _≾?_ to _≾ʰᶠ?_)
open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.RightSided
  Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˢᶜ_; _≾?_ to _≾ˢᶜ?_)

open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost
  using (_≼ˢ_; _≼ˢ?_; _≽ˢ_; _≽ˢ?_)

order : Grade._≾_ mixed-two-sided ≡ _≾ᵐⁱ_
order = refl

------------------------------------------------------------------------
-- Closing a claim by running a decision procedure
--
-- The intervals are taken explicitly: the decision has to be run on
-- known endpoints before the `True` witness can be filled in.

holdsᵐ : (i j : MixedInterval) {p : True (i ≾ᵐⁱ? j)} → i ≾ᵐⁱ j
holdsᵐ i j {p} = toWitness p

failsᵐ : (i j : MixedInterval) {p : False (i ≾ᵐⁱ? j)} → ¬ (i ≾ᵐⁱ j)
failsᵐ i j {p} = toWitnessFalse p

holdsᶠ : {P Q : NeTraces} {p : True (P ≾ᶠ? Q)} → P ≾ᶠ Q
holdsᶠ {p = p} = toWitness p

failsᶠ : {P Q : NeTraces} {p : False (P ≾ᶠ? Q)} → ¬ (P ≾ᶠ Q)
failsᶠ {p = p} = toWitnessFalse p

holdsᶜ : {P Q : NeTraces} {p : True (P ≾ᶜ? Q)} → P ≾ᶜ Q
holdsᶜ {p = p} = toWitness p

failsʰᶠ : {P Q : NeTraces} {p : False (P ≾ʰᶠ? Q)} → ¬ (P ≾ʰᶠ Q)
failsʰᶠ {p = p} = toWitnessFalse p

failsˢᶜ : {P Q : NeTraces} {p : False (P ≾ˢᶜ? Q)} → ¬ (P ≾ˢᶜ Q)
failsˢᶜ {p = p} = toWitnessFalse p

fails≼ˢ : {xs ys : _} {p : False (xs ≼ˢ? ys)} → ¬ (xs ≼ˢ ys)
fails≼ˢ {p = p} = toWitnessFalse p

fails≽ˢ : {xs ys : _} {p : False (xs ≽ˢ? ys)} → ¬ (xs ≽ˢ ys)
fails≽ˢ {p = p} = toWitnessFalse p

------------------------------------------------------------------------
-- A grade as a contract
--
-- `[ { ⌈ read ⌉ } , { ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ } ]` asks every run
-- to take a reading and to fit inside the uplink schedule. A program
-- with one run meets it when that run lies between the two endpoints.
-- Where one fails, the other endpoint is stated too, so which half does
-- the rejecting is decided rather than described.

polling-meets-it :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
polling-meets-it = holdsᵐ _ _

uplinking-meets-it :
  [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
uplinking-meets-it = holdsᵐ _ _

-- a second transmission leaves the schedule, though it does take a
-- reading: the cap rejects it and the floor does not

transmitting-twice-fails :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ])
transmitting-twice-fails = failsᵐ _ _

transmitting-twice-does-read :
  ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ≾ᶠ ⟅ ⌈ read ⌉ ⟆
transmitting-twice-does-read = holdsᶠ

-- nine ticks of idling stay inside the schedule and take no reading:
-- this time it is the floor that rejects

idling-fails :
  ¬ ([ ⟅ ⟨ 9 ⟩ ⟆ , ⟅ ⟨ 9 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ])
idling-fails = failsᵐ _ _

idling-fits-the-schedule : ⟅ ⟨ 9 ⟩ ⟆ ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
idling-fits-the-schedule = holdsᶜ

-- and a run that logs the reading first takes a reading but performs a
-- write the schedule never mentions: the cap again

logging-first-fails :
  ¬ ([ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆ , ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ])
logging-first-fails = failsᵐ _ _

logging-first-does-read : ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ⟆ ≾ᶠ ⟅ ⌈ read ⌉ ⟆
logging-first-does-read = holdsᶠ

------------------------------------------------------------------------
-- As a resource grade: what opens a box
--
-- The same intervals, read as resource grades. `unbox`'s premise
--
--   ρ' ≾ᵣ ρ
--
-- has `ρ'` the product of the locks standing to the variable's right --
-- what elapsed -- and `ρ` the grade on the box. Both endpoints speak,
-- so a box states two conditions at once:
--
--   floor of ρ   whatever elapsed met one of these demands
--                                                    -- it is ready
--   cap of ρ     whatever elapsed stayed within one of these allowances
--                                                    -- it has not expired
--
-- Both are universal in `ρ'`: every run the elapsing computation may
-- have had has to qualify. And `ρ` stands on the weaker side of `≾`, so
-- listing further demands or further allowances makes a box easier to
-- open, not harder.

-- the elapsed grade is the product of the locks: a read, two ticks and
-- a transmission compose into the one run that has happened

elapsed-is-the-product-of-the-locks :
  traces (lo ([ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ]
              ·ᵐⁱ [ ⟅ ⟨ 2 ⟩ ⟆ , ⟅ ⟨ 2 ⟩ ⟆ , tt ]
              ·ᵐⁱ [ ⟅ ⌈ send ⌉ ⟆ , ⟅ ⌈ send ⌉ ⟆ , tt ]))
  ≡ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∷ []
elapsed-is-the-product-of-the-locks = refl

-- A box ready once a reading has been taken, and only until a second
-- transmission: `[ { ⌈ read ⌉ } , { ⌈ read ⌉ ∙ ⌈ send ⌉ } ]`. Reading
-- opens it, and so does reading and transmitting once.

reading-opens-it :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
reading-opens-it = holdsᵐ _ _

transmitting-once-opens-it :
  [ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
transmitting-once-opens-it = holdsᵐ _ _

-- a second transmission and the resource has expired: the box's cap
-- rejects what elapsed, though its floor is still met

expired :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ])
expired = failsᵐ _ _

-- the floor alone would have opened it, which is what a resource grade
-- keeping one endpoint cannot see

expired-is-still-ready : ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ≾ᶠ ⟅ ⌈ read ⌉ ⟆
expired-is-still-ready = holdsᶠ

-- five ticks of idling are the other way round: within the cap, and no
-- reading, so the box is not ready yet

not-yet-ready :
  ¬ ([ ⟅ ⟨ 5 ⟩ ⟆ , ⟅ ⟨ 5 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ])
not-yet-ready = failsᵐ _ _

not-yet-ready-is-in-time : ⟅ ⟨ 5 ⟩ ⟆ ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
not-yet-ready-is-in-time = holdsᶜ

-- both conditions are universal in what elapsed, so a computation with
-- two possible runs opens the box only when both of them qualify

both-branches-open-it :
  [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
both-branches-open-it = holdsᵐ _ _

one-branch-is-not-enough :
  ¬ ([ ⟅ ⌈ read ⌉ ∣ ⟨ 5 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∣ ⟨ 5 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ])
one-branch-is-not-enough = failsᵐ _ _

-- a box with two ways of becoming ready -- a reading, or twenty ticks
-- -- is opened by two unrelated elapsed grades, each on its own demand

ready-on-the-reading :
  [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
      , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 20 ⟩ ⟆ , tt ]
ready-on-the-reading = holdsᵐ _ _

ready-on-the-ticks :
  [ ⟅ ⟨ 20 ⟩ ⟆ , ⟅ ⟨ 20 ⟩ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
      , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 20 ⟩ ⟆ , tt ]
ready-on-the-ticks = holdsᵐ _ _

-- and one computation that may do either opens it with every endpoint
-- of both grades listing alternatives: its uplinking run is admitted by
-- the read and by the uplink schedule, its idling run by the twenty
-- ticks at both endpoints

either-run-opens-it :
  [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 20 ⟩ ⟆
  , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 20 ⟩ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
      , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 20 ⟩ ⟆ , tt ]
either-run-opens-it = holdsᵐ _ _

-- shorten that idle to nine ticks and its branch becomes ready for
-- nothing the box lists, so the box stays shut for the whole
-- computation, however well the other branch qualifies

one-short-branch-shuts-it :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆
        , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⟨ 20 ⟩ ⟆ , tt ])
one-short-branch-shuts-it = failsᵐ _ _

------------------------------------------------------------------------
-- As an effect grade: what `coerce` may do
--
-- Effect grades annotate computations, and `coerce` takes a computation
-- typed at `ε` to any `ε'` with `ε ≾ₑ ε'`. A program with one run has
-- that run at both endpoints, and weakening lowers the floor to a
-- smaller demand or offers a further one, and raises the cap to a
-- larger schedule or offers a further one. Neither direction reverses,
-- so a coercion may forget what a computation did and what it was
-- allowed to do, and may claim neither.

drop-the-floor :
  [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
drop-the-floor = holdsᵐ _ _

-- a second way of meeting the floor, which this run never takes, is
-- harmless: the members are read disjunctively

add-a-demand :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
      , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
add-a-demand = holdsᵐ _ _

-- and so is a second allowance

add-an-allowance :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆ , tt ]
add-an-allowance = holdsᵐ _ _

-- the floor may not ask for more than the run does: the uplink banks
-- nine ticks, not ten

no-stronger-floor :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⟨ 10 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ])
no-stronger-floor = failsᵐ _ _

-- nor may the cap be narrowed

no-narrower-cap :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ])
no-narrower-cap = failsᵐ _ _

-- `return`'s grade is the empty run at both endpoints. It fits under
-- any cap, the empty run being within every schedule ...

pure-fits-any-cap :
  [ ⟅ ε ⟆ , ⟅ ε ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ε ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
pure-fits-any-cap =
  holdsᵐ [ ⟅ ε ⟆ , ⟅ ε ⟆ , tt ]
         [ ⟅ ε ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]

-- ... but it may claim no floor beyond the empty demand: nothing but
-- the empty run meets the empty run

pure-guarantees-nothing :
  ¬ ([ ⟅ ε ⟆ , ⟅ ε ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ])
pure-guarantees-nothing =
  failsᵐ [ ⟅ ε ⟆ , ⟅ ε ⟆ , tt ]
         [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]

-- with alternatives at every endpoint at once. A computation that
-- either takes a reading or idles nine ticks, weakened to "every run
-- reads or passes five ticks, and every run stays within a read and a
-- transmission or within nine ticks". Each of its two runs is carried
-- by a *different* member at either endpoint: the reading by the read
-- and by the transmission's allowance, the idle by the five ticks and
-- by the nine.

crosswise-at-both-endpoints :
  [ ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⟨ 5 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
crosswise-at-both-endpoints = holdsᵐ _ _

-- and every listed member is doing work: without the five ticks the
-- idling run meets no demand ...

floor-needs-both :
  ¬ ([ ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ])
floor-needs-both = failsᵐ _ _

-- ... and without the nine ticks it leaves every allowance, banking
-- seven where nine elapsed

cap-needs-both :
  ¬ ([ ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⟨ 5 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ])
cap-needs-both = failsᵐ _ _

-- sub-effecting a part sub-effects the whole, the product being
-- monotone in both arguments: weakening the uplink to its contract
-- weakens the sequence that goes on to store the reading

weakening-under-sequencing :
  ([ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
   ·ᵐⁱ [ ⟅ ⌈ write ⌉ ⟆ , ⟅ ⌈ write ⌉ ⟆ , tt ])
  ≾ᵐⁱ ([ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
       ·ᵐⁱ [ ⟅ ⌈ write ⌉ ⟆ , ⟅ ⌈ write ⌉ ⟆ , tt ])
weakening-under-sequencing = holdsᵐ _ _

------------------------------------------------------------------------
-- Sequencing multiplies the alternatives
--
-- The monoid is the language product at each endpoint. A phase that
-- either reads or writes, followed by one that either transmits or
-- idles a tick, has four runs -- each run of the first sequenced with
-- each run of the second, in that order.

sequencing-multiplies :
  traces (lo ([ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ , tt ]
              ·ᵐⁱ
              [ ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ , ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ , tt ]))
  ≡   ⌈ read ⌉  ∙ ⌈ send ⌉ ∷ ⌈ read ⌉  ∙ ⟨ 1 ⟩
    ∷ ⌈ write ⌉ ∙ ⌈ send ⌉ ∷ ⌈ write ⌉ ∙ ⟨ 1 ⟩ ∷ []
sequencing-multiplies = refl

-- the cap is the same four, sequenced the same way

sequencing-multiplies-the-cap :
  traces (hi ([ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ , tt ]
              ·ᵐⁱ
              [ ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ , ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ , tt ]))
  ≡   ⌈ read ⌉  ∙ ⌈ send ⌉ ∷ ⌈ read ⌉  ∙ ⟨ 1 ⟩
    ∷ ⌈ write ⌉ ∙ ⌈ send ⌉ ∷ ⌈ write ⌉ ∙ ⟨ 1 ⟩ ∷ []
sequencing-multiplies-the-cap = refl

-- and the four collapse again on the way out: every one of them takes
-- at least a tick, and every one fits inside a run that writes, reads
-- and transmits

four-runs-one-contract :
  ([ ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ , ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ , tt ]
   ·ᵐⁱ
   [ ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ , ⟅ ⌈ send ⌉ ∣ ⟨ 1 ⟩ ⟆ , tt ])
  ≾ᵐⁱ [ ⟅ ⟨ 1 ⟩ ⟆ , ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ]
four-runs-one-contract = holdsᵐ _ _

------------------------------------------------------------------------
-- One set, trimmed in opposite directions at the two ends
--
-- `{ ⌈ read ⌉ , ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ }` is a chain: a run
-- meeting the uplink demand takes a reading too. As a *floor* the
-- uplink is then the redundant member, and as a *cap* the read is --
-- each endpoint keeps the generators it needs, minimal below and
-- maximal above. Both trimmings are reversible, the two grades ordering
-- each other.

trims :
  [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
trims = holdsᵐ _ _

untrims :
  [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
      , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
untrims = holdsᵐ _ _

-- keeping the other member instead is not available at either end: the
-- floor may not keep the uplink alone, nor the cap the read alone

not-the-maximal-floor :
  ¬ ([ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
        , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ])
not-the-maximal-floor = failsᵐ _ _

not-the-minimal-cap :
  ¬ ([ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ⟆ , tt ])
not-the-minimal-cap = failsᵐ _ _

------------------------------------------------------------------------
-- A set that cannot be trimmed at all
--
-- `{ ⌈ read ⌉ ∙ ⌈ send ⌉ , ⌈ send ⌉ ∙ ⌈ read ⌉ }` is an antichain --
-- the same two operations in opposite orders, and a demanded operation
-- is met only by that operation occurring, in order. So neither member
-- is redundant at either endpoint, and the two-element set is the
-- smallest grade saying what it says.

antichain-floor-left :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
        , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ , tt ])
antichain-floor-left = failsᵐ _ _

antichain-floor-right :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
        , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ , tt ])
antichain-floor-right = failsᵐ _ _

antichain-cap-left :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
        , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆ , tt ])
antichain-cap-left = failsᵐ _ _

antichain-cap-right :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆
        , ⟅ ⌈ send ⌉ ∙ ⌈ read ⌉ ⟆ , tt ])
antichain-cap-right = failsᵐ _ _

------------------------------------------------------------------------
-- Two demands, both load-bearing
--
-- A computation that either transmits promptly or idles nine ticks,
-- against a floor listing a read and nine ticks. Each run is carried by
-- a different demand -- the prompt run takes a reading, the idling run
-- passes the time -- and neither demand serves both, the prompt run
-- banking only 1 + 6 = 7 ticks.

crosswise :
  [ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
crosswise = holdsᵐ _ _

-- the read alone leaves the idling run uncovered

read-alone :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ])
read-alone = failsᵐ _ _

-- and nine ticks alone leave the prompt run uncovered

nine-ticks-alone :
  ¬ ([ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆
     , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ]
    ≾ᵐⁱ [ ⟅ ⟨ 9 ⟩ ⟆ , ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∣ ⟨ 9 ⟩ ⟆ , tt ])
nine-ticks-alone = failsᵐ _ _

------------------------------------------------------------------------
-- Why the consistency field is the existential one
--
-- `_◇ˢ_` asks some demand of the floor to fit inside some allowance of
-- the cap. The two lifted candidates -- `LowerLift.TwoSided`'s
-- `L ≼ˢ U` and `UpperLift.TwoSided`'s `L ≽ˢ U` -- would each refuse one
-- of the weakenings above, which the order allows: the first refuses
-- the junk demand added by `add-a-demand`, which fits inside no
-- allowance, and the second the junk allowance added by
-- `add-an-allowance`, which has no demand inside it.

junk-demand-not-≼ˢ :
  ¬ (traces ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
     ≼ˢ traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
junk-demand-not-≼ˢ = fails≼ˢ

junk-allowance-not-≽ˢ :
  ¬ (traces ⟅ ⌈ read ⌉ ⟆
     ≽ˢ traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆)
junk-allowance-not-≽ˢ = fails≽ˢ

-- both pairs are consistent in the sense the grade uses, which is what
-- the `tt`s in those two coercions already recorded

junk-demand-◇ˢ :
  traces ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
  ◇ˢ traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
junk-demand-◇ˢ = tt

junk-allowance-◇ˢ :
  traces ⟅ ⌈ read ⌉ ⟆
  ◇ˢ traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
junk-allowance-◇ˢ = tt

------------------------------------------------------------------------
-- Against the pure columns
--
-- The mixed grade's endpoints are the two the other columns do not put
-- together, and each is visible in a claim its neighbour decides the
-- other way. The runs are the uplink at both.

-- one listed demand carries the floor ...

disjunctive-floor :
  ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ᶠ ⟅ ⌈ write ⌉ ∣ ⟨ 9 ⟩ ⟆
disjunctive-floor = holdsᶠ

-- ... where `LowerLift`'s floor would ask for both, and the uplink
-- performs no write

conjunctive-floor :
  ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ʰᶠ ⟅ ⌈ write ⌉ ∣ ⟨ 9 ⟩ ⟆)
conjunctive-floor = failsʰᶠ

-- a further allowance need not be used ...

disjunctive-cap :
  ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  ≾ᶜ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆
disjunctive-cap = holdsᶜ

-- ... where `UpperLift`'s cap would ask it to be realised, and no run
-- of this grade stays within a lone write

realised-cap :
  ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
     ≾ˢᶜ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆)
realised-cap = failsˢᶜ

-- so the coercion that neither pure column admits holds in this one

both-at-once :
  [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ , tt ]
  ≾ᵐⁱ [ ⟅ ⌈ write ⌉ ∣ ⟨ 9 ⟩ ⟆
      , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆ , tt ]
both-at-once = holdsᵐ _ _
