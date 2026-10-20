-------------------------------------------------------------------------
-- Two-sided trace intervals: a coverage floor under an allowance cap. --
--                                                                     --
-- `Example.Traces.Lifted.TwoSided` at the order `_≼ᶜ_` of             --
-- `Traces.Coverage` below and the order `_≼ᵃ_` of `Traces.Allowance`  --
-- above. A grade `[ P , Q ]` states:                                  --
--                                                                     --
--   whatever the computation did, it covered one of the traces in `P` --
--   and stayed within one of the traces in `Q`                        --
--                                                                     --
-- with both sets read disjunctively, so that both weaken by gaining   --
-- members. `Example.Traces.Timed.LeftSided` and                       --
-- `Example.Traces.Timed.RightSided` are its two endpoints on their    --
-- own.                                                                --
--                                                                     --
-- The floor credits an operation with `costˡᵒ`, the least time it can --
-- take, and the cap charges it `costʰⁱ`, the most. Only the cap       --
-- requires positive costs, under which an empty allowance permits     --
-- only the empty run.                                                 --
--                                                                     --
-- The coherence field, run consistency, is decided by walking a       --
-- guarantee and an allowance together (`Traces.RunConsistency`).      --
-------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Relation.Nullary using (¬_)

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Example.Traces.Timed.TwoSided
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ costʰⁱ : Op → Duration.Carrier D)
  (cost-≤ : (o : Op) → TimeDomain._≤ᴰ_ T (costˡᵒ o) (costʰⁱ o))
  (costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ Duration.0ᴰ D)) where

open import Syntax.Grades.Traces.Coverage.AsOrder
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (coverageOrder)
open import Syntax.Grades.Traces.Coverage T Op costˡᵒ using (duration-≼ᶜ)

open import Syntax.Grades.Traces.Allowance.AsOrder
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (allowanceOrder)
open import Syntax.Grades.Traces.Allowance T Op costʰⁱ using (duration-≼ᵃ)

open import Syntax.Grades.Traces.RunConsistency T Op costˡᵒ costʰⁱ cost-≤
  using (module DecConsistency)
open DecConsistency _≟ₒ_ using (_⋈?_)

open import Syntax.Grades.Example.Traces.Lifted.TwoSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤
  coverageOrder allowanceOrder duration-≼ᶜ duration-≼ᵃ _⋈?_ public
