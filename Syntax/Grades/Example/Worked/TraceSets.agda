------------------------------------------------------------------------
-- Worked instances of the three trace-set grades.                     --
--                                                                     --
-- Every claim below is stated with the *grade order* `_≾_` of the      --
-- grade it belongs to, in the form `unbox` reads it:                   --
--                                                                     --
--     ρ' ≾ ρ    with  ρ' the effects that actually elapsed             --
--                and  ρ  the grade on the box being opened             --
--                                                                     --
-- so each line answers: does *this much having happened* open *that    --
-- box*? Claims and refutations are both closed by running the decision --
-- procedure, so an example asserted the wrong way round does not       --
-- typecheck.                                                           --
--                                                                     --
-- One submodule per grade, in the order they are defined, and a final  --
-- one comparing them on shared pairs. The one-sided grades are         --
-- mirror images: `LeftSided` reads a grade as a floor under what must  --
-- have happened, `RightSided` as a cap on what may have.               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.TraceSets where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; fromWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.Subtrace Op cost
  using (_≼_; module DecSubtrace)
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost using (_≼ˢ_; _≽ˢ_)
open DecSubtrace _≟ₒ_ using (_≼?_)

open WithDecEq _≟ₒ_ using (_∈?_)

------------------------------------------------------------------------
-- Runs the examples use
--
-- `abcd` and its relatives are the abstract shapes; the rest are the
-- sensor node's own runs, from `Worked.Operations`.

abcd abc bc : Trace
abcd = ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉
abc  = ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉
bc   = ⌈ write ⌉ ∙ ⌈ send ⌉

-- Membership of a listed grade, in the `True`-of-a-decision form the
-- orders are phrased in. Refuting an ordering means feeding it one of
-- the elapsed grade's runs: what comes back is a decision that has
-- already computed to `no`, hence absurd.

mem : (P : NeTraces) (s : Trace) → s ∈ traces P → True (s ∈? traces P)
mem P s m = fromWitness {a? = s ∈? traces P} m

------------------------------------------------------------------------
-- Sets of traces ordered by inclusion
--
-- `Grades.Example.TraceSet.Inclusion`. A demand is discharged only by
-- having done literally one of the runs listed, so nothing that appeals
-- to the sub-trace preorder is available here.

module Inclusion where

  open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
    using (traces-by-inclusion; _≾_) public

  -- the abbreviation is the grade's own order

  order : Grade._≾_ traces-by-inclusion ≡ _≾_
  order = refl

  -- a claim, from a map of the listed runs

  listed : {P Q : NeTraces}
         → ({s : Trace} → s ∈ traces P → s ∈ traces Q) → P ≾ Q
  listed f s m = fromWitness (f (toWitness m))

  -- doing exactly what is listed opens the box

  same-run : set₁ uplink ≾ set₁ uplink
  same-run = listed λ { (here refl) → here refl }

  one-of-several : set₁ uplink ≾ set₂ poll uplink
  one-of-several = listed λ { (here refl) → there (here refl) }

  -- doing more does not, because "more" is not on the list

  did-more : ¬ (set₁ abcd ≾ set₁ abc)
  did-more rel = rel abcd (mem (set₁ abcd) abcd (here refl))

  -- nor does spending the time an operation would have taken

  time-for-op : ¬ (set₁ ⌈ read ⌉ ≾ set₁ ⟨ 1 ⟩)
  time-for-op rel = rel ⌈ read ⌉ (mem (set₁ ⌈ read ⌉) ⌈ read ⌉ (here refl))

  -- and doing less certainly does not

  did-less : ¬ (set₁ poll ≾ set₁ uplink)
  did-less rel = rel poll (mem (set₁ poll) poll (here refl))

------------------------------------------------------------------------
-- Sets of traces ordered up to the sub-trace preorder
--
-- `Grades.Example.TraceSet.LeftSided`: a set of alternative demands,
-- discharged by having done at least what one of them asks for.

module LeftSided where

  open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ cost
    using (left-sided-traces; _≾_) public

  order : Grade._≾_ left-sided-traces ≡ _≾_
  order = refl

  -- Between singleton grades the order is decided outright, so a claim
  -- and its refutation are each one line.

  -- a claim between grades, from a witness per elapsed run

  meets : {P Q : NeTraces}
        → ({t : Trace} → t ∈ traces P → Any (_≼ t) (traces Q)) → P ≾ Q
  meets f t m = fromWitness (f (toWitness m))

  infix 4 _≾!_ _⋠!_

  _≾!_ : (s t : Trace) {p : True (t ≼? s)} → set₁ s ≾ set₁ t
  (s ≾! t) {p} = meets {set₁ s} {set₁ t} λ { (here refl) → here (toWitness p) }

  _⋠!_ : (s t : Trace) {p : False (t ≼? s)} → ¬ (set₁ s ≾ set₁ t)
  (s ⋠! t) {p} rel
    with toWitness {a? = any? (λ x → x ≼? s) (traces (set₁ t))}
                   (rel s (mem (set₁ s) s (here refl)))
  ... | here q   = toWitnessFalse p q
  ... | there ()

  ----------------------------------------------------------------------
  -- Doing more than was demanded opens the box

  more-events : set₁ abcd ≾ set₁ abc
  more-events = abcd ≾! abc

  more-of-the-run : set₁ uplink ≾ set₁ ⌈ read ⌉
  more-of-the-run = uplink ≾! ⌈ read ⌉

  ----------------------------------------------------------------------
  -- Doing less does not

  fewer-events : ¬ (set₁ bc ≾ set₁ abcd)
  fewer-events = bc ⋠! abcd

  less-of-the-run : ¬ (set₁ poll ≾ set₁ uplink)
  less-of-the-run = poll ⋠! uplink

  ----------------------------------------------------------------------
  -- Time against operations
  --
  -- A demand for elapsed time is discharged by whatever took that long,
  -- operations included; a demand for an operation is discharged by
  -- nothing but that operation occurring.

  -- a read costs one tick, so having read discharges a one-tick demand

  read-covers-a-tick : set₁ ⌈ read ⌉ ≾ set₁ ⟨ 1 ⟩
  read-covers-a-tick = ⌈ read ⌉ ≾! ⟨ 1 ⟩

  -- but not a two-tick demand, which exceeds its cost

  read-covers-no-more : ¬ (set₁ ⌈ read ⌉ ≾ set₁ ⟨ 2 ⟩)
  read-covers-no-more = ⌈ read ⌉ ⋠! ⟨ 2 ⟩

  -- a write costs three, so it does

  write-covers-two-ticks : set₁ ⌈ write ⌉ ≾ set₁ ⟨ 2 ⟩
  write-covers-two-ticks = ⌈ write ⌉ ≾! ⟨ 2 ⟩

  -- the whole uplink takes nine ticks, and covers a demand for nine

  uplink-covers-nine : set₁ uplink ≾ set₁ ⟨ 9 ⟩
  uplink-covers-nine = uplink ≾! ⟨ 9 ⟩

  uplink-covers-no-ten : ¬ (set₁ uplink ≾ set₁ ⟨ 10 ⟩)
  uplink-covers-no-ten = uplink ⋠! ⟨ 10 ⟩

  -- and the converse never holds: waiting performs nothing

  waiting-is-no-read : ¬ (set₁ ⟨ 1 ⟩ ≾ set₁ ⌈ read ⌉)
  waiting-is-no-read = ⟨ 1 ⟩ ⋠! ⌈ read ⌉

  waiting-is-no-uplink : ¬ (set₁ ⟨ 100 ⟩ ≾ set₁ uplink)
  waiting-is-no-uplink = ⟨ 100 ⟩ ⋠! uplink

  ----------------------------------------------------------------------
  -- Alternatives
  --
  -- The elapsed grade is read for the worst case and the demanded one
  -- for the best: whichever run happened must discharge some listed
  -- demand.

  -- the box offers two ways to be opened, and the uplink takes one

  either-demand : set₁ uplink ≾ set₂ ⌈ read ⌉ ⟨ 20 ⟩
  either-demand =
    meets λ { (here refl) → here (toWitness {a? = ⌈ read ⌉ ≼? uplink} tt) }

  -- but if the node might only have polled, the uplink demand fails

  either-run : ¬ (set₂ poll uplink ≾ set₁ uplink)
  either-run rel = rel poll (mem (set₂ poll uplink) poll (here refl))

------------------------------------------------------------------------
-- (Right) one-sided sets of traces
--
-- `Grades.Example.TraceSet.RightSided`, the mirror image: a set of
-- alternative permissions, and a run stays within the grade by doing at
-- most what one of them allows.

module RightSided where

  open import Syntax.Grades.Example.TraceSet.RightSided Op _≟ₒ_ cost
    using (right-sided-traces; _≾_) public

  order : Grade._≾_ right-sided-traces ≡ _≾_
  order = refl

  permits : {P Q : NeTraces}
          → ({s : Trace} → s ∈ traces P → Any (s ≼_) (traces Q)) → P ≾ Q
  permits f s m = fromWitness (f (toWitness m))

  infix 4 _≾!_ _⋠!_

  _≾!_ : (s t : Trace) {p : True (s ≼? t)} → set₁ s ≾ set₁ t
  (s ≾! t) {p} = permits {set₁ s} {set₁ t} λ { (here refl) → here (toWitness p) }

  _⋠!_ : (s t : Trace) {p : False (s ≼? t)} → ¬ (set₁ s ≾ set₁ t)
  (s ⋠! t) {p} rel
    with toWitness {a? = any? (λ x → s ≼? x) (traces (set₁ t))}
                   (rel s (mem (set₁ s) s (here refl)))
  ... | here q   = toWitnessFalse p q
  ... | there ()

  -- doing less than the cap permits stays within it

  under-the-cap : set₁ poll ≾ set₁ uplink
  under-the-cap = poll ≾! uplink

  -- doing more does not

  over-the-cap : ¬ (set₁ (uplink ∙ ⌈ send ⌉) ≾ set₁ uplink)
  over-the-cap = (uplink ∙ ⌈ send ⌉) ⋠! uplink

  -- a cap naming an operation may be spent on idling instead, at that
  -- operation's execution time -- the mirror of the left-sided grade's
  -- "time discharges a demand for time"

  idle-within-a-read : set₁ ⟨ 1 ⟩ ≾ set₁ ⌈ read ⌉
  idle-within-a-read = ⟨ 1 ⟩ ≾! ⌈ read ⌉

  idle-beyond-a-read : ¬ (set₁ ⟨ 2 ⟩ ≾ set₁ ⌈ read ⌉)
  idle-beyond-a-read = ⟨ 2 ⟩ ⋠! ⌈ read ⌉

  -- but a cap written as pure time permits no operations at all: the
  -- cap is behavioural, not merely temporal

  read-outside-a-tick : ¬ (set₁ ⌈ read ⌉ ≾ set₁ ⟨ 1 ⟩)
  read-outside-a-tick = ⌈ read ⌉ ⋠! ⟨ 1 ⟩

  -- unlike the left-sided grade, the unit is the *least* element here:
  -- it permits nothing but an instantaneous run

  nothing-under-the-unit : ¬ (set₁ ⟨ 1 ⟩ ≾ u)
  nothing-under-the-unit = ⟨ 1 ⟩ ⋠! ε

------------------------------------------------------------------------
-- Sets of traces ordered by the convex (Egli-Milner) lift
--
-- `Grades.Example.TraceSet.Convex`. The order above, plus the demand
-- that every listed alternative be achievable by a run already present.

module Convex where

  open import Syntax.Grades.Example.TraceSet.Convex Op _≟ₒ_ cost
    using (traces-convex; _≾_) public

  order : Grade._≾_ traces-convex ≡ _≾_
  order = refl

  -- the two halves, each from a witness

  achieves : {P Q : NeTraces}
           → ({s : Trace} → s ∈ traces Q → Any (s ≼_) (traces P))
           → traces Q ≼ˢ traces P
  achieves f s m = fromWitness (f (toWitness m))

  meets : {P Q : NeTraces}
        → ({t : Trace} → t ∈ traces P → Any (_≼ t) (traces Q))
        → traces Q ≽ˢ traces P
  meets f t m = fromWitness (f (toWitness m))

  infix 4 _≾!_ _⋠!_

  _≾!_ : (s t : Trace) {p : True (t ≼? s)} → set₁ s ≾ set₁ t
  (s ≾! t) {p} =
      achieves {set₁ s} {set₁ t} (λ { (here refl) → here (toWitness p) })
    , meets    {set₁ s} {set₁ t} (λ { (here refl) → here (toWitness p) })

  _⋠!_ : (s t : Trace) {p : False (t ≼? s)} → ¬ (set₁ s ≾ set₁ t)
  (s ⋠! t) {p} (_ , sm)
    with toWitness {a? = any? (λ x → x ≼? s) (traces (set₁ t))}
                   (sm s (mem (set₁ s) s (here refl)))
  ... | here q   = toWitnessFalse p q
  ... | there ()

  -- on singleton grades the two halves coincide, so the order agrees
  -- with the one-sided grade

  more-events : set₁ abcd ≾ set₁ abc
  more-events = abcd ≾! abc

  waiting-is-no-read : ¬ (set₁ ⟨ 1 ⟩ ≾ set₁ ⌈ read ⌉)
  waiting-is-no-read = ⟨ 1 ⟩ ⋠! ⌈ read ⌉

  -- they part company on a demand offering an alternative that nothing
  -- elapsed can achieve: the extra half rejects it

  unreachable-alternative : ¬ (set₁ uplink ≾ set₂ ⌈ read ⌉ ⟨ 20 ⟩)
  unreachable-alternative (h , _) =
    h ⟨ 20 ⟩ (mem (set₂ ⌈ read ⌉ ⟨ 20 ⟩) ⟨ 20 ⟩ (there (here refl)))

------------------------------------------------------------------------
-- How the three orders relate
--
-- Inclusion is contained in the sub-trace order (that containment is a
-- grade morphism -- see `Worked.Systems`), and so is the convex order,
-- which is the sub-trace order plus its Hoare half. Both containments
-- are strict, and inclusion and the convex order are incomparable.

module Comparison where

  open Inclusion using () renaming (_≾_ to _≾ⁱ_)
  open LeftSided using () renaming (_≾_ to _≾ˢ_)
  open Convex    using () renaming (_≾_ to _≾ᶜ_)

  convex⇒subtrace : {P Q : NeTraces} → P ≾ᶜ Q → P ≾ˢ Q
  convex⇒subtrace = proj₂

  -- inclusion accepts what the convex order rejects: an unreachable
  -- alternative in the demand

  incl-not-convex : (set₁ ⟨ 20 ⟩ ≾ⁱ set₂ ⌈ read ⌉ ⟨ 20 ⟩)
                  × ¬ (set₁ ⟨ 20 ⟩ ≾ᶜ set₂ ⌈ read ⌉ ⟨ 20 ⟩)
  incl-not-convex =
      Inclusion.listed (λ { (here refl) → there (here refl) })
    , λ { (h , _) → h ⌈ read ⌉
                      (mem (set₂ ⌈ read ⌉ ⟨ 20 ⟩) ⌈ read ⌉ (here refl)) }

  -- and the convex order accepts what inclusion rejects: doing more
  -- than was listed

  convex-not-incl : (set₁ abcd ≾ᶜ set₁ abc) × ¬ (set₁ abcd ≾ⁱ set₁ abc)
  convex-not-incl = Convex.more-events , Inclusion.did-more
