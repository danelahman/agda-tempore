------------------------------------------------------------------------
-- Worked instances of the count grades, at the sensor node.           --
--                                                                     --
-- One counter per operation, in the order `read`, `write`, `send`.    --
-- An at-most grade is a quota on each -- a rate limit, "at most two   --
-- transmissions" -- and an at-least grade a count that is certain --  --
-- "three readings have been taken", after which a token computed from --
-- them is available.                                                  --
--                                                                     --
-- Every ordering is closed by the grade's own decision procedure, and --
-- every projection by computation, so a claim stated the wrong way    --
-- round does not typecheck.                                           --
------------------------------------------------------------------------

module Syntax.Grades.Example.Counts.Worked where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; []; _∷_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade; _→ᵍ_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans;
         costˡᵒ; costʰⁱ; costʰⁱ-pos;
         Trace; ⌈_⌉; ⟨_⟩; _∙_; ε; poll; logged; uplink; chatty-uplink; idle)

open import Syntax.Grades.Example.Time.RightSided using (𝕀ᵣ; [0,_]; ↑_; ∞)
open import Syntax.Grades.Example.Time.LeftSided using (𝕀)

import Syntax.Grades.Example.Counts.AtMost as AtMost
import Syntax.Grades.Example.Counts.AtLeast as AtLeast

open AtMost using (at-most-counts; upto; unlimited)
open AtLeast using (at-least-counts; atleast)

------------------------------------------------------------------------
-- The counters

index : Op → Fin 3
index read  = zero
index write = suc zero
index send  = suc (suc zero)

-- a grade is written as its three coordinates

Quota : Set
Quota = Vec 𝕀ᵣ 3

⟪_,_,_⟫ᵐ : 𝕀ᵣ → 𝕀ᵣ → 𝕀ᵣ → Quota
⟪ r , w , s ⟫ᵐ = r ∷ w ∷ s ∷ []

Certain : Set
Certain = Vec 𝕀 3

⟪_,_,_⟫ˡ : ℕ → ℕ → ℕ → Certain
⟪ r , w , s ⟫ˡ = atleast r ∷ atleast w ∷ atleast s ∷ []

------------------------------------------------------------------------
-- At most: quotas
--
-- A larger quota is weaker, `unlimited` lifts one quota and keeps the
-- others, and a quota on one operation says nothing about another.

module Quotas where

  open AtMost using (_≾ᵛ_; _≾ᵛ?_; _·ᵛ_; _⊔ᵛ_; uᵛ; ⊤ᵛ)

  holds : {c d : Quota} {p : True (c ≾ᵛ? d)} → c ≾ᵛ d
  holds {p = p} = toWitness p

  fails : {c d : Quota} {p : False (c ≾ᵛ? d)} → ¬ (c ≾ᵛ d)
  fails {p = p} = toWitnessFalse p

  -- `unlimited` leaves too little of a coordinate for the implicit
  -- arguments to be found, so the grades are given explicitly where it
  -- appears

  holdsᵉ : (c d : Quota) {p : True (c ≾ᵛ? d)} → c ≾ᵛ d
  holdsᵉ c d {p} = toWitness p

  failsᵉ : (c d : Quota) {p : False (c ≾ᵛ? d)} → ¬ (c ≾ᵛ d)
  failsᵉ c d {p} = toWitnessFalse p

  -- one reading and two transmissions fit a limit of two of each, with
  -- writes unrestricted

  within-limit : ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ ≾ᵛ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ
  within-limit = holdsᵉ ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ

  -- a third transmission does not

  over-limit : ¬ (⟪ upto 1 , upto 0 , upto 3 ⟫ᵐ ≾ᵛ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ)
  over-limit = failsᵉ ⟪ upto 1 , upto 0 , upto 3 ⟫ᵐ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ

  -- two readings and one transmission are incomparable: each quota
  -- exceeds the other on one counter

  reads-vs-sends : ¬ (⟪ upto 2 , upto 0 , upto 0 ⟫ᵐ ≾ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
  reads-vs-sends = fails

  sends-vs-reads : ¬ (⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ≾ᵛ ⟪ upto 2 , upto 0 , upto 0 ⟫ᵐ)
  sends-vs-reads = fails

  -- sequencing adds the quotas, `unlimited` absorbing

  sequenced : ⟪ upto 1 , upto 0 , upto 1 ⟫ᵐ ·ᵛ ⟪ upto 1 , unlimited , upto 0 ⟫ᵐ
            ≡ ⟪ upto 2 , unlimited , upto 1 ⟫ᵐ
  sequenced = refl

  -- the join takes the greater quota on each counter, so it can exceed
  -- both grades together

  joined : ⟪ upto 2 , upto 0 , upto 0 ⟫ᵐ ⊔ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ
         ≡ ⟪ upto 2 , upto 0 , upto 1 ⟫ᵐ
  joined = refl

  -- the unit is least and `unlimited` everywhere is greatest

  none-least : uᵛ ≾ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ
  none-least = holds

  unlimited-greatest : ⟪ upto 5 , unlimited , upto 9 ⟫ᵐ ≾ᵛ ⊤ᵛ
  unlimited-greatest = holdsᵉ ⟪ upto 5 , unlimited , upto 9 ⟫ᵐ ⊤ᵛ

------------------------------------------------------------------------
-- At least: certain counts
--
-- A smaller demand is weaker, and demanding nothing is the greatest
-- grade.

module Certain-counts where

  open AtLeast using (_≾ᵛ_; _≾ᵛ?_; _·ᵛ_; _⊔ᵛ_; uᵛ)

  holds : {c d : Certain} {p : True (c ≾ᵛ? d)} → c ≾ᵛ d
  holds {p = p} = toWitness p

  fails : {c d : Certain} {p : False (c ≾ᵛ? d)} → ¬ (c ≾ᵛ d)
  fails {p = p} = toWitnessFalse p

  -- three readings certain is enough for a token asking for one

  three-readings : ⟪ 3 , 0 , 0 ⟫ˡ ≾ᵛ ⟪ 1 , 0 , 0 ⟫ˡ
  three-readings = holds

  -- one reading is not enough for a token asking for three

  one-reading : ¬ (⟪ 1 , 0 , 0 ⟫ˡ ≾ᵛ ⟪ 3 , 0 , 0 ⟫ˡ)
  one-reading = fails

  -- a certain transmission does not stand in for a reading

  send-for-read : ¬ (⟪ 0 , 0 , 1 ⟫ˡ ≾ᵛ ⟪ 1 , 0 , 0 ⟫ˡ)
  send-for-read = fails

  -- sequencing adds the certain counts; the join keeps only what both
  -- make certain

  sequenced : ⟪ 1 , 0 , 1 ⟫ˡ ·ᵛ ⟪ 2 , 1 , 0 ⟫ˡ ≡ ⟪ 3 , 1 , 1 ⟫ˡ
  sequenced = refl

  joined : ⟪ 3 , 1 , 0 ⟫ˡ ⊔ᵛ ⟪ 1 , 0 , 2 ⟫ˡ ≡ ⟪ 1 , 0 , 0 ⟫ˡ
  joined = refl

  -- demanding nothing is the greatest grade, and it is the unit

  nothing-greatest : ⟪ 3 , 1 , 2 ⟫ˡ ≾ᵛ uᵛ
  nothing-greatest = holds

------------------------------------------------------------------------
-- The subset cap, projected onto quotas
--
-- Each counter takes the greatest count among the listed runs.

module Subsets-to-quotas where

  open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
    using (permitting_; any-run)
  open import Syntax.Grades.Example.Worked.Operations using (⟅_⟆; ⟅_∣_⟆)
  open import Syntax.Grades.Example.System.Counts.Subsets.AtMost
    Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans index
    using (subsets→at-most-counts)

  open _→ᵍ_ subsets→at-most-counts using (map)

  -- a reading, and possibly a transmission

  poll-or-uplink : map (permitting ⟅ poll ∣ uplink ⟆) ≡ ⟪ upto 1 , upto 0 , upto 1 ⟫ᵐ
  poll-or-uplink = refl

  -- transmitting twice

  chatty : map (permitting ⟅ chatty-uplink ⟆) ≡ ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ
  chatty = refl

  -- a write or a transmission: each counter is maximised on its own,
  -- so the quota allows both, which neither run performs

  write-or-send : map (permitting ⟅ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆) ≡ ⟪ upto 0 , upto 1 , upto 1 ⟫ᵐ
  write-or-send = refl

  -- idling draws on nothing, and any run at all needs no quota

  idling : map (permitting ⟅ idle ⟆) ≡ ⟪ upto 0 , upto 0 , upto 0 ⟫ᵐ
  idling = refl

  unrestricted : map any-run ≡ ⟪ unlimited , unlimited , unlimited ⟫ᵐ
  unrestricted = refl

------------------------------------------------------------------------
-- The subset cap, projected onto certain counts
--
-- Each counter takes the least count among the listed runs, and any
-- run at all makes no claim.

module Subsets-to-certain-counts where

  open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
    using (permitting_; any-run)
  open import Syntax.Grades.Example.Worked.Operations using (⟅_⟆; ⟅_∣_⟆)
  open import Syntax.Grades.Example.System.Counts.Subsets.AtLeast
    Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans index
    using (subsets→at-least-counts-with-⊤)
  open AtLeast using (certainly; no-claim)

  open _→ᵍ_ subsets→at-least-counts-with-⊤ using (map)

  -- polling or uplinking: the reading is certain, the transmission not

  poll-or-uplink :
    map (permitting ⟅ poll ∣ uplink ⟆) ≡ certainly 1 ∷ certainly 0 ∷ certainly 0 ∷ []
  poll-or-uplink = refl

  unrestricted : map any-run ≡ no-claim ∷ no-claim ∷ no-claim ∷ []
  unrestricted = refl

------------------------------------------------------------------------
-- The coverage floor, projected onto certain counts
--
-- Each counter takes the least count among the listed guarantees.

module Floor-to-certain-counts where

  open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
    using (⟅_⟆; ⟅_∣_⟆)
  open import Syntax.Grades.Example.System.Counts.Timed.LeftSided
    Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ index
    using (left-sided→at-least-counts)

  open _→ᵍ_ left-sided→at-least-counts using (map)

  -- stored or transmitted: the reading is certain, neither of the rest

  logged-or-uplink : map ⟅ logged ∣ uplink ⟆ ≡ ⟪ 1 , 0 , 0 ⟫ˡ
  logged-or-uplink = refl

  -- two transmissions certain

  chatty : map ⟅ chatty-uplink ⟆ ≡ ⟪ 1 , 0 , 2 ⟫ˡ
  chatty = refl

  -- a guarantee of time alone makes no count certain

  idling : map ⟅ idle ⟆ ≡ ⟪ 0 , 0 , 0 ⟫ˡ
  idling = refl

------------------------------------------------------------------------
-- The allowance cap: time buys operations
--
-- The bound `⟨ 2 ⟩` permits a reading, as it covers its one tick. Any
-- grade morphism into quotas sends `⟨ 2 ⟩` to the unit, so it sends
-- `⌈ read ⌉` to the unit too.

module Allowance-cap where

  open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
    using (within_; ⟅_⟆; _≾_; holds)
  open import Syntax.Grades.Example.System.Counts.Timed.RightSided
    Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos index
    using (erases; miscounts)

  a-delay-permits-a-reading : within ⟅ ⌈ read ⌉ ⟆ ≾ within ⟅ ⟨ 2 ⟩ ⟆
  a-delay-permits-a-reading = holds

  reading-erased : (F : _ →ᵍ at-most-counts 3) → _→ᵍ_.map F (within ⟅ ⌈ read ⌉ ⟆) ≡ AtMost.uᵛ
  reading-erased F = erases F read

------------------------------------------------------------------------
-- A cost model does not preserve the join
--
-- Weigh each counter by its worst-case execution time, 1, 3 and 6
-- ticks. A write weighs 3 and a transmission 6, but their join, one of
-- each, weighs 9: more than either.

module Cost-model where

  open import Syntax.Grades.Example.System.Counts.Time using (module WeighRight)
  open WeighRight using (weigh)
  open AtMost using (_⊔ᵛ_)
  open import Syntax.Grades.Example.Time.RightSided using (_⊔ₒ_)

  slow : Vec _ 3
  slow = 1 ∷ 3 ∷ 6 ∷ []

  a-write : weigh slow ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ≡ upto 3
  a-write = refl

  a-send : weigh slow ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ≡ upto 6
  a-send = refl

  join-of-images : weigh slow ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ₒ weigh slow ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ
                 ≡ upto 6
  join-of-images = refl

  image-of-join : weigh slow (⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
                ≡ upto 9
  image-of-join = refl

  join-not-preserved :
    ¬ (weigh slow (⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
       ≡ weigh slow ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ₒ weigh slow ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
  join-not-preserved ()
