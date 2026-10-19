------------------------------------------------------------------------
-- Running times of operations, and the costs they give.              --
--                                                                    --
-- Each operation runs for a duration in an interval of the time      --
-- domain, each end open or closed. Every operation takes some time:  --
-- its lower end lies at or above the cut just above zero, so the     --
-- interval admits positive durations only. The trace orders read the --
-- closed hull of the interval: an operation is credited with its     --
-- least running time, the lower end, and charged its most, the upper --
-- end, which must therefore be finite.                               --
------------------------------------------------------------------------

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Traces.RunningTimes
  {D : Duration} (T : TimeDomain D) (Op : Set) where

open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

open import Util.Equality

open import Syntax.Durations.Monus T
  using (Carrier; 0ᴰ; _≤ᴰ_; ≤ᴰ-refl; ≤ᴰ-trans)
open import Syntax.Durations.Intervals T

-- an upper end that is a cut, not the absence of a bound

data Bounded : Hi → Set where
  fin : (c : Cut) → Bounded (fin c)

record RunningTimes : Set where
  field
    rt         : Op → Interval
    rt-bounded : (o : Op) → Bounded (hi (rt o))
    -- every operation takes some time: its lower end is above zero
    rt-positive : (o : Op) → 0⁺ ⊑ lo (rt o)

  -- so its upper end is above zero too

  rt-takes-time : (o : Op) → ¬ (hi (rt o) ⊑ʰ fin 0⁺)
  rt-takes-time o with hi (rt o) | lo◁hi (rt o)
  ... | fin c | p = λ q → ⊑-⊏-trans (rt-positive o) p q
  ... | ∞     | _ = λ ()

  -- the closed hull, as costs

  costˡᵒ : Op → Carrier
  costˡᵒ o = pt (lo (rt o))

  costʰⁱ : Op → Carrier
  costʰⁱ o with hi (rt o) | rt-bounded o
  ... | fin c | fin .c = pt c

  cost-≤ : (o : Op) → costˡᵒ o ≤ᴰ costʰⁱ o
  cost-≤ o with hi (rt o) | rt-bounded o | lo◁hi (rt o)
  ... | fin c | fin .c | p = ⊑⇒≤ (⊏⇒⊑ p)

  costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ 0ᴰ)
  costʰⁱ-pos o with hi (rt o) | rt-bounded o | rt-takes-time o
  ... | fin (p ∣ s) | fin ._ | ¬z = λ e → ¬z (by-side e ≤ˢ-⁺)
