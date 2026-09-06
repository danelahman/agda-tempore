------------------------------------------------------------------------
-- Worked instances of the three trace-set grades.                     --
--                                                                     --
-- All three have the same carrier -- a non-empty finite set of timed   --
-- traces -- and the same monoid. They differ only in what weakening a  --
-- grade is allowed to do.                                             --
--                                                                     --
-- The examples are laid out the way `unbox` reads them. Its premise is --
-- `ρ' ≾ᵣ ρ`, where `ρ'` records the effects that actually elapsed and  --
-- `ρ` is the grade on the box being opened, so each row below asks:    --
-- does *this much having happened* discharge *that demand*?            --
--                                                                     --
--                                            inclusion sub-trace convex --
--   { uplink } ≾ { ⌈read⌉ }                     no      yes     yes   --
--   { poll }   ≾ { uplink }                     no      no      no    --
--   { uplink } ≾ { ⌈read⌉ , ⟨ 9 ⟩ }             no      yes     no    --
--   { ⌈read⌉ } ≾ { ⌈read⌉ , ⟨ 9 ⟩ }             yes     yes     no    --
--                                                                     --
-- Rows 1 and 4 show inclusion and the convex order are incomparable,   --
-- and both sit inside the sub-trace order. Reading down: inclusion     --
-- discharges a demand only by having done literally one of the runs    --
-- listed; the sub-trace order discharges it by having done at least    --
-- what one of them asks for; and the convex order additionally         --
-- requires every listed demand to be achievable by something the       --
-- elapsed grade offers.                                                --
--                                                                     --
-- No row lets *less* than the demand discharge it -- that is the point --
-- of the direction, and row 2 is the witness.                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.TraceSets where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_,_; proj₂)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; fromWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.Subtrace Op cost
  using (_≼_; module DecSubtrace)
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost
  using (_≼ˢ_; _≽ˢ_; u-≽ˢ)
open DecSubtrace _≟ₒ_ using (_≼?_)

open WithDecEq _≟ₒ_ using (_∈?_)

open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
  using (right-sided-traces) renaming (_≾_ to _≾ⁱ_)

open import Syntax.Grades.Example.TraceSet.UpToSubtrace Op _≟ₒ_ cost
  using (traces-up-to-subtrace) renaming (_≾_ to _≾ˢ_)

open import Syntax.Grades.Example.TraceSet.Convex Op _≟ₒ_ cost
  using (traces-convex) renaming (_≾_ to _≾ᶜ_)

-- the three abbreviations above are exactly the orders the three grades
-- carry, so every example below is a fact about the grades themselves

order-of-inclusion : Grade._≾_ right-sided-traces ≡ _≾ⁱ_
order-of-inclusion = refl

order-of-subtrace : Grade._≾_ traces-up-to-subtrace ≡ _≾ˢ_
order-of-subtrace = refl

order-of-convex : Grade._≾_ traces-convex ≡ _≾ᶜ_
order-of-convex = refl

------------------------------------------------------------------------
-- Running the decision procedures
--
-- `s ≼! t` asserts a sub-trace fact and closes it by running `_≼?_`;
-- `s ⋠! t` asserts its negation and closes it by running the same
-- decision the other way. An example claimed the wrong way round simply
-- will not typecheck, so the tables here are checked, not asserted.

infix 4 _≼!_ _⋠!_

_≼!_ : (s t : Trace) {p : True (s ≼? t)} → s ≼ t
(s ≼! t) {p} = toWitness p

_⋠!_ : (s t : Trace) {p : False (s ≼? t)} → ¬ (s ≼ t)
(s ⋠! t) {p} = toWitnessFalse p

-- The set-level orders quantify over *all* traces, so they are not
-- themselves decidable. Each is nevertheless determined by a finite
-- amount of data, which these three take as input.

-- inclusion: a membership map

incl : {P Q : NeTraces}
     → ({s : Trace} → s ∈ traces P → s ∈ traces Q) → P ≾ⁱ Q
incl f s m = fromWitness (f (toWitness m))

-- the sub-trace order: every run of `P` meets some demand of `Q`

meets : {P Q : NeTraces}
      → ({t : Trace} → t ∈ traces P → Any (_≼ t) (traces Q)) → P ≾ˢ Q
meets f t m = fromWitness (f (toWitness m))

-- the extra half the convex order asks for: every demand of `Q` is
-- achieved by some run of `P`

achieves : {P Q : NeTraces}
         → ({s : Trace} → s ∈ traces Q → Any (s ≼_) (traces P))
         → traces Q ≼ˢ traces P
achieves f s m = fromWitness (f (toWitness m))

-- To refute an ordering, feed it a run of the elapsed grade: what comes
-- back is a decision that has already computed to `no`, hence absurd.

mem : (P : NeTraces) (s : Trace) → s ∈ traces P → True (s ∈? traces P)
mem P s m = fromWitness {a? = s ∈? traces P} m

------------------------------------------------------------------------
-- What the sub-trace preorder does and does not allow
--
-- Slack is created only by absorbing a *delay* of the right-hand trace,
-- and it pays for anything on the left. Read as "the demand `s` is
-- discharged by having done `t`", that means a demand for an operation
-- is discharged by enough time passing, but a demand for time is not
-- discharged by having spent it on operations.

-- the uplink does a read, and idles for the two ticks it idles for

read-done : ⌈ read ⌉ ≼ uplink
read-done = ⌈ read ⌉ ≼! uplink

idle-done : ⟨ 2 ⟩ ≼ uplink
idle-done = ⟨ 2 ⟩ ≼! uplink

-- but not a third tick of idling, though the uplink takes nine ticks
-- in all: the rest of that time went on operations

idle-not-done : ¬ (⟨ 3 ⟩ ≼ uplink)
idle-not-done = ⟨ 3 ⟩ ⋠! uplink

nine-not-done : ¬ (⟨ 9 ⟩ ≼ uplink)
nine-not-done = ⟨ 9 ⟩ ⋠! uplink

-- conversely, a demand for an operation *is* discharged by time, at the
-- operation's execution time: a write costs three ticks

write-by-waiting : ⌈ write ⌉ ≼ ⟨ 3 ⟩
write-by-waiting = ⌈ write ⌉ ≼! ⟨ 3 ⟩

write-needs-three : ¬ (⌈ write ⌉ ≼ ⟨ 2 ⟩)
write-needs-three = ⌈ write ⌉ ⋠! ⟨ 2 ⟩

-- a shorter run does not discharge a demand for a longer one

uplink-not-by-poll : ¬ (uplink ≼ poll)
uplink-not-by-poll = uplink ⋠! poll

------------------------------------------------------------------------
-- Row 1: doing more than was demanded
--
-- `{ uplink } ≾ { ⌈read⌉ }`: the box asks that a reading have been
-- taken, and the elapsed uplink took one -- along with a good deal
-- more. Inclusion cannot see that, because the uplink is not literally
-- the listed run; both cost-aware orders can.

did-uplink demand-read : NeTraces
did-uplink  = set₁ uplink
demand-read = set₁ ⌈ read ⌉

more-not-inclusion : ¬ (did-uplink ≾ⁱ demand-read)
more-not-inclusion rel = rel uplink (mem did-uplink uplink (here refl))

more-subtrace : did-uplink ≾ˢ demand-read
more-subtrace = meets λ { (here refl) → here read-done }

more-convex : did-uplink ≾ᶜ demand-read
more-convex = achieves (λ { (here refl) → here read-done })
            , meets    (λ { (here refl) → here read-done })

------------------------------------------------------------------------
-- Row 2: doing less than was demanded
--
-- `{ poll } ≾ { uplink }` fails in all three orders. This is the
-- direction the whole reading turns on: having merely polled does not
-- discharge a box that asks for a full uplink.

did-poll demand-uplink : NeTraces
did-poll      = set₁ poll
demand-uplink = set₁ uplink

less-not-inclusion : ¬ (did-poll ≾ⁱ demand-uplink)
less-not-inclusion rel = rel poll (mem did-poll poll (here refl))

less-not-subtrace : ¬ (did-poll ≾ˢ demand-uplink)
less-not-subtrace rel = rel poll (mem did-poll poll (here refl))

less-not-convex : ¬ (did-poll ≾ᶜ demand-uplink)
less-not-convex rel = less-not-subtrace (proj₂ rel)

-- nor does spending the same amount of time a different way: the uplink
-- takes nine ticks, and still does not discharge a demand for nine
-- ticks of waiting

did-uplink-vs-waiting : ¬ (did-uplink ≾ˢ set₁ ⟨ 9 ⟩)
did-uplink-vs-waiting rel = rel uplink (mem did-uplink uplink (here refl))

------------------------------------------------------------------------
-- Row 3: a demand with an unachievable alternative
--
-- `{ uplink } ≾ { ⌈read⌉ , ⟨ 9 ⟩ }`: the box offers two ways to be
-- opened and the uplink takes the first. The sub-trace order is content
-- with that. The convex order is not: it also asks that every listed
-- alternative be achievable by some run the elapsed grade offers, and
-- nothing the uplink does amounts to nine ticks of waiting.

demand-either : NeTraces
demand-either = set₂ ⌈ read ⌉ ⟨ 9 ⟩

either-subtrace : did-uplink ≾ˢ demand-either
either-subtrace = meets λ { (here refl) → here read-done }

either-not-convex : ¬ (did-uplink ≾ᶜ demand-either)
either-not-convex (h , _) =
  h ⟨ 9 ⟩ (mem demand-either ⟨ 9 ⟩ (there (here refl)))

------------------------------------------------------------------------
-- Row 4: the same demand, discharged by inclusion
--
-- `{ ⌈read⌉ } ≾ { ⌈read⌉ , ⟨ 9 ⟩ }` holds for inclusion outright, and
-- hence for the sub-trace order. It still fails convexly, for the same
-- reason as row 3 -- which is what makes inclusion and the convex order
-- incomparable, row 1 being the other direction.

did-read : NeTraces
did-read = set₁ ⌈ read ⌉

listed-inclusion : did-read ≾ⁱ demand-either
listed-inclusion = incl λ { (here refl) → here refl }

listed-subtrace : did-read ≾ˢ demand-either
listed-subtrace = meets λ { (here refl) → here (⌈ read ⌉ ≼! ⌈ read ⌉) }

listed-not-convex : ¬ (did-read ≾ᶜ demand-either)
listed-not-convex (h , _) =
  h ⟨ 9 ⟩ (mem demand-either ⟨ 9 ⟩ (there (here refl)))

------------------------------------------------------------------------
-- How the three orders are related
--
-- The convex order is the sub-trace order plus its Hoare half, so it is
-- contained in it. Inclusion is contained in it too (that containment
-- is a grade morphism -- see `Worked.Systems`). Rows 1 and 4 show the
-- two containments are strict and that inclusion and the convex order
-- are incomparable.

convex⇒subtrace : {P Q : NeTraces} → P ≾ᶜ Q → P ≾ˢ Q
convex⇒subtrace = proj₂

------------------------------------------------------------------------
-- The monoid, which all three share
--
-- Sequencing two grades is the language product: every run of the first
-- followed by every run of the second.

-- polling and then writing is the logged run

seq-runs : set₁ poll · set₁ ⌈ write ⌉ ≡ set₁ logged
seq-runs = refl

-- the unit demands nothing, and `n` time steps is the singleton set
-- containing the pure delay of length `n`

trace-unit : Grade.u traces-up-to-subtrace ≡ set₁ ⟨ 0 ⟩
trace-unit = refl

trace-of-nat : Grade.of-nat traces-up-to-subtrace 2 ≡ set₁ ⟨ 2 ⟩
trace-of-nat = refl

-- every grade discharges the unit's demand, so `{ ε }` is the greatest
-- grade -- exactly as `[ 0 ,+∞⟩` is the greatest left-sided interval

anything-meets-unit : did-uplink ≾ˢ u
anything-meets-unit = u-≽ˢ (traces did-uplink)

-- a two-run grade sequenced with a one-run grade has two runs

seq-branches : traces (set₂ poll uplink · set₁ ⟨ 1 ⟩)
             ≡ (poll ∙ ⟨ 1 ⟩) ∷ (uplink ∙ ⟨ 1 ⟩) ∷ []
seq-branches = refl
