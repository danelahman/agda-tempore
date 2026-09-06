------------------------------------------------------------------------
-- Worked instances of the three trace-set grades.                     --
--                                                                     --
-- All three have the same carrier -- a non-empty finite set of timed   --
-- traces -- and the same monoid. They differ only in what weakening a  --
-- grade is allowed to add, and the examples below pin that down:       --
--                                                                     --
--                                        inclusion  sub-trace  convex  --
--   { uplink }   ≾ { poll , uplink }         yes       yes       no    --
--   { uplink }   ≾ { ⟨ 9 ⟩ }                 no        yes       yes   --
--   { ⟨ 9 ⟩ }    ≾ { uplink }                no        no        no    --
--   { poll , uplink } ≾ { poll , logged , uplink }                     --
--                                            yes       yes       yes   --
--                                                                     --
-- So inclusion and the convex order are *incomparable*, and both are   --
-- contained in the sub-trace order, which is the coarsest of the       --
-- three. Reading down the first column: inclusion cares only about     --
-- which runs are listed; the sub-trace order lets a run be replaced by --
-- anything that fits inside its time budget; and the convex order      --
-- allows that only between runs already present, so it cannot be       --
-- weakened by offering a strictly faster run.                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.TraceSets where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_,_; proj₁)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; fromWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.Subtrace Op cost using (_≼_)
open import Syntax.Grades.Traces.Subtrace Op cost using (module DecSubtrace)
open DecSubtrace _≟ₒ_ using (_≼?_)

open WithDecEq _≟ₒ_ using (_∈?_)

open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
  using (right-sided-traces) renaming (_≾_ to _≾ⁱ_)

open import Syntax.Grades.Example.TraceSet.UpToSubtrace Op _≟ₒ_ cost
  using (_≼ˢ_; traces-up-to-subtrace) renaming (_≾_ to _≾ˢ_)

open import Syntax.Grades.Example.TraceSet.Convex Op _≟ₒ_ cost
  using (_≽ˢ_; traces-convex) renaming (_≾_ to _≾ᶜ_)

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
-- will not typecheck, so the tables below are checked, not asserted.

infix 4 _≼!_ _⋠!_

_≼!_ : (s t : Trace) {p : True (s ≼? t)} → s ≼ t
(s ≼! t) {p} = toWitness p

_⋠!_ : (s t : Trace) {p : False (s ≼? t)} → ¬ (s ≼ t)
(s ⋠! t) {p} = toWitnessFalse p

-- The set-level orders quantify over *all* traces, so they are not
-- themselves decidable. Each is nevertheless determined by a finite
-- amount of data, which these three take as input: a membership map for
-- inclusion, a covering for the Hoare half, and a co-covering for the
-- Smyth half.

incl : {P Q : NeTraces}
     → ({s : Trace} → s ∈ traces P → s ∈ traces Q) → P ≾ⁱ Q
incl f s m = fromWitness (f (toWitness m))

hoare : {xs ys : List Trace}
      → ({s : Trace} → s ∈ xs → Any (s ≼_) ys) → xs ≼ˢ ys
hoare f s m = fromWitness (f (toWitness m))

smyth : {xs ys : List Trace}
      → ({t : Trace} → t ∈ ys → Any (_≼ t) xs) → xs ≽ˢ ys
smyth f t m = fromWitness (f (toWitness m))

-- To refute an ordering, feed it a run of the smaller grade: what comes
-- back is a decision that has already computed to `no`, hence absurd.
-- `mem P s` is the membership premise those refutations need, in the
-- `True`-of-a-decision form the orders are phrased in.

mem : (P : NeTraces) (s : Trace) → s ∈ traces P → True (s ∈? traces P)
mem P s m = fromWitness {a? = s ∈? traces P} m

------------------------------------------------------------------------
-- What the sub-trace preorder does and does not allow
--
-- Slack is created only by absorbing a *delay* of the right-hand trace,
-- and it pays for anything on the left. So the whole uplink run fits
-- inside a nine-tick budget -- its operations are charged the time they
-- take -- while a nine-tick delay does not fit inside the uplink run,
-- whose only delay is the two ticks it idles for.

-- the operations of the left-hand trace are paid for by time on the right

uplink-fits : uplink ≼ ⟨ 9 ⟩
uplink-fits = uplink ≼! ⟨ 9 ⟩

-- and not by less time than they take: the uplink needs all nine ticks

uplink-needs-9 : ¬ (uplink ≼ ⟨ 8 ⟩)
uplink-needs-9 = uplink ⋠! ⟨ 8 ⟩

-- the operations of the *right-hand* trace pay for nothing: only the
-- two ticks the uplink idles for are available as slack

delay-fits : ⟨ 2 ⟩ ≼ uplink
delay-fits = ⟨ 2 ⟩ ≼! uplink

delay-does-not-fit : ¬ (⟨ 3 ⟩ ≼ uplink)
delay-does-not-fit = ⟨ 3 ⟩ ⋠! uplink

-- so, although the uplink takes nine ticks, it does not meet a schedule
-- that asks for nine ticks to elapse

no-op-for-delay : ¬ (⟨ 9 ⟩ ≼ uplink)
no-op-for-delay = ⟨ 9 ⟩ ⋠! uplink

-- deleting operations on the right is free, which is what makes the
-- shorter runs sub-traces of the longer ones

poll-below-logged : poll ≼ logged
poll-below-logged = poll ≼! logged

poll-below-uplink : poll ≼ uplink
poll-below-uplink = poll ≼! uplink

------------------------------------------------------------------------
-- Row 1: offering a strictly faster run
--
-- `{ uplink } ≾ { poll , uplink }`. Inclusion and the sub-trace order
-- both allow it. The convex order does not: `poll` is faster than
-- everything the smaller grade offers, so the Smyth half has nothing to
-- cover it with.

only-uplink poll-or-uplink : NeTraces
only-uplink    = set₁ uplink
poll-or-uplink = set₂ poll uplink

faster-inclusion : only-uplink ≾ⁱ poll-or-uplink
faster-inclusion = incl λ { (here refl) → there (here refl) }

faster-subtrace : only-uplink ≾ˢ poll-or-uplink
faster-subtrace = hoare λ { (here refl) → there (here (uplink ≼! uplink)) }

-- `poll` is a member of the larger grade, and the Smyth half would have
-- to cover it from the smaller one -- that is, `uplink ≼ poll`. The
-- decision procedure says no, so the premise is already absurd.

faster-not-convex : ¬ (only-uplink ≾ᶜ poll-or-uplink)
faster-not-convex (_ , sm) = sm poll (mem poll-or-uplink poll (here refl))

------------------------------------------------------------------------
-- Row 2: replacing a run by a budget it fits in
--
-- `{ uplink } ≾ { ⟨ 9 ⟩ }`. Inclusion fails -- the uplink is simply not
-- a member -- but both cost-aware orders accept it, because the uplink
-- fits inside nine ticks and nine ticks is covered by the uplink from
-- the other side too.

budget : NeTraces
budget = set₁ ⟨ 9 ⟩

budget-not-inclusion : ¬ (only-uplink ≾ⁱ budget)
budget-not-inclusion rel = rel uplink (mem only-uplink uplink (here refl))

budget-subtrace : only-uplink ≾ˢ budget
budget-subtrace = hoare λ { (here refl) → here uplink-fits }

budget-convex : only-uplink ≾ᶜ budget
budget-convex =
    hoare (λ { (here refl) → here uplink-fits })
  , smyth (λ { (here refl) → here uplink-fits })

------------------------------------------------------------------------
-- Row 3: asking for time to pass, and doing work instead
--
-- `{ ⟨ 9 ⟩ } ≾ { uplink }` fails in all three orders. This is the one
-- asymmetry the cost-aware orders keep: a schedule that calls for nine
-- ticks of *waiting* is not met by nine ticks of *working*.

work-not-inclusion : ¬ (budget ≾ⁱ only-uplink)
work-not-inclusion rel = rel ⟨ 9 ⟩ (mem budget ⟨ 9 ⟩ (here refl))

work-not-subtrace : ¬ (budget ≾ˢ only-uplink)
work-not-subtrace rel = rel ⟨ 9 ⟩ (mem budget ⟨ 9 ⟩ (here refl))

work-not-convex : ¬ (budget ≾ᶜ only-uplink)
work-not-convex rel = work-not-subtrace (proj₁ rel)

------------------------------------------------------------------------
-- Row 4: offering a run between two already present
--
-- `{ poll , uplink } ≾ { poll , logged , uplink }`. All three orders
-- accept it. The convex order does because `logged` is covered from
-- below by `poll`, which the smaller grade already offers -- this is
-- exactly what "convex" means: weakening may fill in, but not extend.

with-logged : NeTraces
with-logged = set₃ poll logged uplink

between-inclusion : poll-or-uplink ≾ⁱ with-logged
between-inclusion =
  incl λ { (here refl)        → here refl
         ; (there (here refl)) → there (there (here refl)) }

between-convex : poll-or-uplink ≾ᶜ with-logged
between-convex =
    hoare (λ { (here refl)         → here (poll ≼! poll)
             ; (there (here refl)) → there (there (here (uplink ≼! uplink))) })
  , smyth (λ { (here refl)                 → here (poll ≼! poll)
             ; (there (here refl))         → here poll-below-logged
             ; (there (there (here refl))) → there (here (uplink ≼! uplink)) })

between-subtrace : poll-or-uplink ≾ˢ with-logged
between-subtrace = proj₁ between-convex

------------------------------------------------------------------------
-- How the three orders are related
--
-- The convex order is the sub-trace order plus its Smyth half, so it is
-- contained in it. Inclusion is contained in it too (that containment
-- is a grade morphism -- see `Worked.Systems`). Rows 1 and 2 show the
-- two containments are strict, and that inclusion and the convex order
-- are incomparable: row 1 holds for inclusion but not convexly, row 2
-- convexly but not for inclusion.

convex⇒subtrace : {P Q : NeTraces} → P ≾ᶜ Q → P ≾ˢ Q
convex⇒subtrace = proj₁

------------------------------------------------------------------------
-- The monoid, which all three share
--
-- Sequencing two grades is the language product: every run of the first
-- followed by every run of the second.

-- polling and then writing is the logged run

seq-runs : set₁ poll · set₁ ⌈ write ⌉ ≡ set₁ logged
seq-runs = refl

-- the unit is the singleton set containing the empty run, and `n` time
-- steps is the singleton set containing the pure delay of length `n`

trace-unit : Grade.u right-sided-traces ≡ set₁ ⟨ 0 ⟩
trace-unit = refl

trace-of-nat : Grade.of-nat right-sided-traces 2 ≡ set₁ ⟨ 2 ⟩
trace-of-nat = refl

-- a two-run grade sequenced with a one-run grade has two runs

seq-branches : traces (poll-or-uplink · set₁ ⟨ 1 ⟩)
             ≡ (poll ∙ ⟨ 1 ⟩) ∷ (uplink ∙ ⟨ 1 ⟩) ∷ []
seq-branches = refl
