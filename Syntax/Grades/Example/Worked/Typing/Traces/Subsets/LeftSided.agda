------------------------------------------------------------------------
-- Typed example computations at the grade of demanded runs.           --
--                                                                     --
-- A grade `P` is read against the runs `X` a computation may have as   --
-- `P ⊆ X`: every listed trace is a run it can exhibit. The set is read --
-- *conjunctively*, so weakening drops members and `⟅ ε ⟆` demands only --
-- that stopping be possible -- which is still a demand, so no          --
-- written-out list is above them all. `no-demand` is.                  --
--                                                                     --
-- The calculus meets this grade at its most rigid. Every operation is  --
-- graded by a singleton, products of singletons are singletons, and a  --
-- grade below a singleton is a non-empty subset of it, hence that      --
-- singleton again: so every computation's grade is exactly its run and --
-- `coerce` has nothing to do. `unbox` inherits that -- a box is        --
-- claimable only after precisely the run it names -- and `if` inherits --
-- something sharper still: `no-common-listed-grade` below shows that   --
-- no *listed* grade types a conditional whose branches perform         --
-- different operations, since the two coercions would make one         --
-- non-empty set a subset of two disjoint singletons. `no-demand`       --
-- does type it, demanding no run at all; what `if` can do below it     --
-- is branch over *data*, both branches making the same run.            --
--                                                                     --
-- The comments inside the programs say what each former appends to the --
-- context its subcomputation is typed in: `⟨ ρ ⟩` a lock, `∷ A` a      --
-- binding. The locks between a box's binding and its `unbox` multiply  --
-- to the run that elapsed, and here that run has to be the run the box --
-- demands, exactly.                                                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Traces.Subsets.LeftSided where

open import Data.Empty using (⊥)
open import Data.List.Base using () renaming (_∷_ to _∷ˡ_; [] to []ˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using ()
  renaming (here to hereᴬ; there to thereᴬ)
open import Data.Product using (Σ; _,_)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_;
         Trace; NeTraces; neTraces; traces; ε; _∙_; ⌈_⌉; ⟨_⟩;
         ⟅_⟆; ⟅_∣_⟆; ⟅_∣_∣_⟆)

open import Syntax.Grades.Example.Worked.Traces.Subsets.LeftSided
  using (left-sided; Demands; demanding_; no-demand;
         holds; fails; holdsᵉ; failsᵉ)

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_
  using (∈-⊑; ⊑-∈)

------------------------------------------------------------------------
-- The operations, graded by the run that performs them

opTime : Op → Demands
opTime o = demanding ⟅ ⌈ o ⌉ ⟆

open import Syntax.Grades.Example.Worked.Typing.Core left-sided opTime

------------------------------------------------------------------------
-- Effectful computations
--
-- The grade of a computation is the one run it makes, demanded, and the
-- locks along it are that run one event at a time.

sampling : [] ⊢C⦂ Reading ‼ demanding ⟅ ⌈ read ⌉ ⟆
sampling =
  perform read ⋆         -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
storing =
  perform read ⋆         -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform write here  -- ⟨ demanding ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
relaying =
  perform read ⋆         -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (perform send here   -- ⟨ demanding ⟅ ⌈ send ⌉ ⟆ ⟩ ∷ Unit
      (return ⋆))

tagged-relaying : [] ∷ NodeId ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
tagged-relaying =
  perform read ⋆         -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (match ⦉ eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd)) , here ⦊
                         -- ∷ NodeId ∷ Reading
      `in perform send here (return ⋆))

------------------------------------------------------------------------
-- Readings go stale
--
-- `ρ ≾ᵣ uᵣ` asks the empty run to be among the elapsed ones, which it
-- is only where no lock stands in the way.

reading-stale-after-an-operation : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-an-operation = fails

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-natʳ 2 ≾ᵣ uᵣ)
reading-stale-after-idling = fails

carried-id : [] ∷ NodeId ⊢C⦂ NodeId ‼ demanding ⟅ ⌈ read ⌉ ⟆
carried-id =
  perform read ⋆         -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
    (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ Hd))))

------------------------------------------------------------------------
-- Sub-effecting
--
-- Weakening drops demands, so a grade below a singleton is a non-empty
-- subset of it: the singleton itself. A deterministic computation
-- therefore has nowhere to be coerced to.

adding-a-demand :
  ¬ (opTime read ·ₑ uₑ ≾ₑ demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆)
adding-a-demand = fails

trading-work-for-time : ¬ (opTime read ·ₑ uₑ ≾ₑ demanding ⟅ ⟨ 1 ⟩ ⟆)
trading-work-for-time = fails

------------------------------------------------------------------------
-- Conditional branching
--
-- No *listed* grade types a conditional whose branches perform
-- different operations: a common one would have to be a non-empty
-- subset of both branches' singletons. `no-demand` is not a list and
-- does type it.

-- a non-empty set has a member

member : (P : NeTraces) → Σ Trace (_∈ traces P)
member (neTraces (t ∷ˡ _) _) = t , hereᴬ refl

-- and membership of a singleton pins it down

only-member : {s t : Trace} → s ∈ (t ∷ˡ []ˡ) → s ≡ t
only-member (hereᴬ p) = p

no-common-listed-grade : (grade : NeTraces)
                       → opTime send  ·ₑ uₑ ≾ₑ demanding grade
                       → opTime write ·ₑ uₑ ≾ₑ demanding grade
                       → ⊥
no-common-listed-grade grade send-fits write-fits with member grade
... | t , t∈grade with only-member (∈-⊑ send-fits t∈grade)
...   | refl with only-member (∈-⊑ write-fits t∈grade)
...     | ()

-- `no-demand` is a common grade: it demands no run at all, so
-- both branches weaken to it

transmitting-fits-the-top : opTime send ·ₑ uₑ ≾ₑ no-demand
transmitting-fits-the-top = ≾-⊤ₑ (opTime send ·ₑ uₑ)

storing-fits-the-top : opTime write ·ₑ uₑ ≾ₑ no-demand
storing-fits-the-top = ≾-⊤ₑ (opTime write ·ₑ uₑ)

-- so the conditional every list of demands refuses is typed at `no-demand`,
-- each branch coerced to the grade that demands nothing

branching-at-the-top : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ no-demand
branching-at-the-top =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce transmitting-fits-the-top (perform send  here (return ⋆))
    `else coerce storing-fits-the-top      (perform write here (return ⋆))

-- the three grades one would reach for, refuted one at a time

storing-branch-at-the-transmission :
  ¬ (opTime write ·ₑ uₑ ≾ₑ demanding ⟅ ⌈ send ⌉ ⟆)
storing-branch-at-the-transmission = fails

transmitting-branch-at-the-store :
  ¬ (opTime send ·ₑ uₑ ≾ₑ demanding ⟅ ⌈ write ⌉ ⟆)
transmitting-branch-at-the-store = fails

neither-at-the-union :
  ¬ (opTime send ·ₑ uₑ ≾ₑ demanding ⟅ ⌈ send ⌉ ∣ ⌈ write ⌉ ⟆)
neither-at-the-union = fails

-- what `if` can do here is branch over data: both branches make the
-- same run, so they are already at one grade, and neither locks the
-- context

either-reading :
  [] ∷ Bool ∷ Reading ∷ Reading ⊢C⦂ Unit ‼ demanding ⟅ ⌈ send ⌉ ⟆
either-reading =
  if eternal-var Boolₑ (Tl-∷ (Tl-∷ Hd))
    `then perform send here (return ⋆)
    `else perform send (fresh-var ≾ᵣ-refl (Tl-∷ Hd)) (return ⋆)

------------------------------------------------------------------------
-- Unboxing: a resource demanding exactly its run
--
-- `unbox`'s premise `elapsed ≾ᵣ ρ` asks every run the box demands to
-- be one the computation exhibited. With both sides singletons that is
-- equality: the locks between the binding and the claim have to
-- multiply to the run the box names.

demand : R
demand = demanding ⟅ ⌈ read ⌉ ⟆

claim-after-sampling : [] ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
claim-after-sampling =
  box {ρ = demand} (const 42)  -- ∷ [ demanding ⟅ ⌈ read ⌉ ⟆ ] Reading
    (perform read ⋆      -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds -- ∷ Reading
        (perform send here (return ⋆))))

handed-over : [] ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
handed-over =
  box {ρ = demand} (const 42)  -- ∷ [ demanding ⟅ ⌈ read ⌉ ⟆ ] Reading
    (lam                 -- ∷ [ demanding ⟅ ⌈ read ⌉ ⟆ ] Reading
       (perform read ⋆   -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
         (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds
                         -- ∷ Reading
           (perform send here (return ⋆))))
      · here)

either-way : [] ∷ Bool ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
either-way =
  box {ρ = demand} (const 42)  -- ∷ [ demanding ⟅ ⌈ read ⌉ ⟆ ] Reading
    (perform read ⋆      -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) holds -- ∷ Reading
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
-- at once, with no lock in between

nothing-demanded : R
nothing-demanded = demanding ⟅ ε ⟆

claiming-now : [] ⊢C⦂ Unit ‼ demanding ⟅ ⌈ send ⌉ ⟆
claiming-now =
  box {ρ = nothing-demanded} (const 42)
                         -- ∷ [ demanding ⟅ ε ⟆ ] Reading
    (unbox Hd (holdsᵉ uᵣ nothing-demanded)
                         -- ∷ Reading
      (perform send here (return ⋆)))

------------------------------------------------------------------------
-- Every claim here is an equality
--
-- The claims above all compare a grade with itself: a computation's
-- grade is the singleton of its run, and `elapsed ≾ᵣ ρ` asks
-- `ρ ⊆ elapsed`, so there is no room for the non-reflexive comparisons
-- the ordered families allow.

-- `no-demand` demands no run at all

_∈ᵈ_ : Trace → R → Set
s ∈ᵈ (demanding P) = s ∈ traces P
s ∈ᵈ no-demand       = ⊥

every-demand-is-the-elapsed-run :
  (t : Trace) (ρ : R) → demanding ⟅ t ⟆ ≾ᵣ ρ → (s : Trace) → s ∈ᵈ ρ → s ≡ t
every-demand-is-the-elapsed-run t (demanding ρ) sub s s∈ρ =
  only-member (∈-⊑ sub s∈ρ)

-- so a box demanding two runs is out of reach of any one of them, and
-- of every program in this calculus

two-run-demand : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆)
two-run-demand = fails

------------------------------------------------------------------------
-- Non-singleton grades
--
-- A grade with several members demands each of them separately, which
-- sets this floor apart from the other five endpoints: there the union
-- of two grades is their join, here it is their *meet*. The calculus
-- cannot hand a computation such a grade, but the order is defined on
-- them all the same, and the facts below are what a branching rule
-- taking unions would be working with.

-- weakening drops demands, so a two-run grade sits below each of the
-- singletons it is made of

dropping-the-store :
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ≾ᵣ demanding ⟅ ⌈ read ⌉ ⟆
dropping-the-store = holds

dropping-the-reading :
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ≾ᵣ demanding ⟅ ⌈ write ⌉ ⟆
dropping-the-reading = holds

-- and it is the greatest grade that does: anything demanding both runs
-- demands the union, so the union is their meet

union-is-the-meet :
  (P : R) → P ≾ᵣ demanding ⟅ ⌈ read ⌉ ⟆
          → P ≾ᵣ demanding ⟅ ⌈ write ⌉ ⟆
          → P ≾ᵣ demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆
union-is-the-meet (demanding P) reads writes = ⊑-∈ step
  where
    step : (s : Trace)
         → s ∈ (⌈ read ⌉ ∷ˡ ⌈ write ⌉ ∷ˡ []ˡ) → s ∈ traces P
    step _ (hereᴬ refl)          = ∈-⊑ reads  (hereᴬ refl)
    step _ (thereᴬ (hereᴬ refl)) = ∈-⊑ writes (hereᴬ refl)

-- a longer list demands more, so it too sits below a shorter one

three-runs-below-two :
  demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆
  ≾ᵣ demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆
three-runs-below-two = holds

two-runs-not-below-three :
  ¬ (demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆
     ≾ᵣ demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆)
two-runs-not-below-three = fails

-- the unit demands only that stopping be possible, so a list that
-- includes the empty run weakens to it -- and no other list does

listing-stopping : demanding ⟅ ε ∣ ⌈ read ⌉ ⟆ ≾ᵣ demanding ⟅ ε ⟆
listing-stopping = holdsᵉ (demanding ⟅ ε ∣ ⌈ read ⌉ ⟆) (demanding ⟅ ε ⟆)

-- sequencing distributes over the demands: each demanded run is
-- followed by what comes next

demands-sequence :
  (demanding ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆ ·ᵣ demanding ⟅ ⌈ send ⌉ ⟆)
  ≾ᵣ demanding ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
demands-sequence = holds

-- None of that is reachable from a program *here*, though. With every
-- operation graded by the single run that performs it, the only
-- non-singleton grade a computation can be given is a list padded with
-- copies of the run that happened -- which demands nothing new:

sampling-listed-twice : [] ⊢C⦂ Reading ‼ demanding ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ⟆
sampling-listed-twice =
  coerce holds
    (perform read ⋆      -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return here))

-- Two *different* runs in one grade have to come from the signature,
-- an operation being asked to have several runs available -- which is
-- what a floor read conjunctively is for.
-- `Subsets.LeftSided.Retrying` grades the transmitter that way, and
-- there the programs, the coercions and the `unbox` premises are all
-- between grades listing two runs.

------------------------------------------------------------------------
-- Unboxing under a branch
--
-- `no-common-listed-grade` settles this too, the resource grades being
-- the same monoid: a box claimed after a reading in one branch and
-- after a transmission in the other would have to demand both runs and
-- neither, leaving `no-demand`, which demands nothing of either.

sampling-branch-demands-its-run :
  uᵣ ·ᵣ opTime read ≾ᵣ demanding ⟅ ⌈ read ⌉ ⟆
sampling-branch-demands-its-run = holds

transmitting-branch-cannot-meet-it :
  ¬ (uᵣ ·ᵣ opTime send ≾ᵣ demanding ⟅ ⌈ read ⌉ ⟆)
transmitting-branch-cannot-meet-it = fails

------------------------------------------------------------------------
-- Programs written at these demands
--
-- The box demands a reading and a store; the run makes exactly that
-- before claiming it -- two locks multiplying to the demanded run --
-- and the `if` afterwards chooses what to transmit without touching
-- the grade.

logged : R
logged = demanding ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆

log-then-claim :
  [] ∷ Bool ⊢C⦂ Unit ‼ demanding ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
log-then-claim =
  box {ρ = logged} (const 42)  -- ∷ [ demanding ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ] Reading
    (perform read ⋆      -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (perform write here  -- ⟨ demanding ⟅ ⌈ write ⌉ ⟆ ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) holds
                         -- ∷ Reading
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
--
-- Handling locks its `in` part by the handled computation's grade,
-- exactly as sequencing does.

forwarded : [] ⊢C⦂ Reading ‼ demanding ⟅ ⌈ read ⌉ ⟆
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                  -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return here)

identified : Node ⊢C⦂ NodeId ‼ demanding ⟅ ⌈ read ⌉ ⟆
identified =
  handle perform read ⋆ (return here)
    `with identifying
    `in                  -- ⟨ demanding ⟅ ⌈ read ⌉ ⟆ ⟩ ∷ Reading
      (return (eternal-var nodeid-eternal (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))))

-- no clause may drop its continuation: its grade demands a run that
-- performs the operation, and returning at once makes the empty run

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding = failsᵉ uₑ (op-grade read ·ₑ uₑ)
