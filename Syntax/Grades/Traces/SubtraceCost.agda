------------------------------------------------------------------------
-- Comparing sub-trace preorders across two different costs            --
--                                                                    --
-- Slack is what pays for the events of the left-hand trace, and a     --
-- larger cost makes an operation more expensive to pay for. Raising   --
-- the cost therefore *narrows* the order: what fits inside a budget    --
-- when operations are slow also fits when they are fast. This is the  --
-- sub-trace counterpart of `duration`'s monotonicity in the cost.     --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (≤-trans; ∸-monoʳ-≤; m+[n∸m]≡n)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceCost
  (Op : Set) (c c' : Op → ℕ) (c≤c' : (o : Op) → c o ≤ c' o) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.SubtraceDuration Op c using (duration-slack)

open Durations c

-- the sub-trace preorders at the two costs, kept apart by renaming

open import Syntax.Grades.Traces.Subtrace Op c
  using (weaken; coe)
  renaming (_≼[_]_ to _≼[_]ᶜ_; _≼_ to _≼ᶜ_;
            nil to nilᶜ; keep to keepᶜ; del-op to del-opᶜ;
            del-delay to del-delayᶜ; use-op to use-opᶜ;
            use-delay to use-delayᶜ)

open import Syntax.Grades.Traces.Subtrace Op c'
  using ()
  renaming (_≼[_]_ to _≼[_]ᶜ'_; _≼_ to _≼ᶜ'_;
            nil to nilᶜ'; keep to keepᶜ'; del-op to del-opᶜ';
            del-delay to del-delayᶜ'; use-op to use-opᶜ';
            use-delay to use-delayᶜ')

------------------------------------------------------------------------
-- Antitonicity in the cost
--
-- Only `use-op` reads the cost. At the smaller one the leading
-- operation is cheaper to cover, and the premise is left with more
-- slack than it asks for -- the surplus is absorbed by `weaken`.

≼-cost-anti : ∀ {k s t} → s ≼[ k ]ᶜ' t → s ≼[ k ]ᶜ t
≼-cost-anti nilᶜ'                      = nilᶜ
≼-cost-anti (keepᶜ' d)                 = keepᶜ (≼-cost-anti d)
≼-cost-anti (del-opᶜ' d)               = del-opᶜ (≼-cost-anti d)
≼-cost-anti (del-delayᶜ' d)            = del-delayᶜ (≼-cost-anti d)
≼-cost-anti {k} (use-opᶜ' {o = o} p d) =
  use-opᶜ (≤-trans (c≤c' o) p)
          (coe eq (weaken ((k ∸ c o) ∸ (k ∸ c' o)) (≼-cost-anti d)))
  where
    eq : (k ∸ c' o) + ((k ∸ c o) ∸ (k ∸ c' o)) ≡ k ∸ c o
    eq = m+[n∸m]≡n (∸-monoʳ-≤ k (c≤c' o))
≼-cost-anti (use-delayᶜ' p d)          = use-delayᶜ p (≼-cost-anti d)

-- the sub-trace order proper (no slack)

≼-cost-anti₀ : {s t : Trace} → s ≼ᶜ' t → s ≼ᶜ t
≼-cost-anti₀ = ≼-cost-anti

------------------------------------------------------------------------
-- Bounding the duration at the smaller cost
--
-- What fits inside a schedule when operations are charged `c'` also
-- fits when they are charged the cheaper `c`, so the smaller cost
-- bounds durations too. Read at the zero cost, this says that only the
-- *delays* of a schedule are ever available to cover a delay.

duration-slack-lo : ∀ {k s t} → s ≼[ k ]ᶜ' t → duration s ≤ duration t + k
duration-slack-lo d = duration-slack (≼-cost-anti d)
