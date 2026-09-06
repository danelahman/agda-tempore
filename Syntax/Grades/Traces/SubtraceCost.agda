------------------------------------------------------------------------
-- Comparing sub-trace preorders across two different costs            --
--                                                                    --
-- Slack is what a run banks from what was not demanded of it, and a   --
-- larger cost makes an unmatched operation bank more. Raising the     --
-- cost therefore *widens* the order: a demand met when operations are --
-- cheap is still met when they are dear. This is the sub-trace        --
-- counterpart of `duration`'s monotonicity in the cost.               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (≤-trans; +-assoc; m+[n∸m]≡n)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceCost
  (Op : Set) (c c' : Op → ℕ) (c≤c' : (o : Op) → c o ≤ c' o) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.SubtraceDuration Op c' using (duration-slack)

open Durations c'

-- the sub-trace preorders at the two costs, kept apart by renaming

open import Syntax.Grades.Traces.Subtrace Op c
  using ()
  renaming (_≼[_]_ to _≼[_]ᶜ_; _≼_ to _≼ᶜ_;
            nil to nilᶜ; keep to keepᶜ; pay-op to pay-opᶜ;
            del-delay to del-delayᶜ; use-delay to use-delayᶜ)

open import Syntax.Grades.Traces.Subtrace Op c'
  using (weaken; coe)
  renaming (_≼[_]_ to _≼[_]ᶜ'_; _≼_ to _≼ᶜ'_;
            nil to nilᶜ'; keep to keepᶜ'; pay-op to pay-opᶜ';
            del-delay to del-delayᶜ'; use-delay to use-delayᶜ')

------------------------------------------------------------------------
-- Monotonicity in the cost
--
-- Only `pay-op` reads the cost. At the larger one the unmatched
-- operation banks more, so the premise is handed more slack than it
-- asks for -- the surplus is absorbed by `weaken`.

≼-cost-mono : ∀ {k s t} → s ≼[ k ]ᶜ t → s ≼[ k ]ᶜ' t
≼-cost-mono nilᶜ                     = nilᶜ'
≼-cost-mono (keepᶜ d)                = keepᶜ' (≼-cost-mono d)
≼-cost-mono {k} (pay-opᶜ {o = o} d)  =
  pay-opᶜ' (coe eq (weaken (c' o ∸ c o) (≼-cost-mono d)))
  where
    eq : (k + c o) + (c' o ∸ c o) ≡ k + c' o
    eq = trans (+-assoc k (c o) (c' o ∸ c o))
               (cong (k +_) (m+[n∸m]≡n (c≤c' o)))
≼-cost-mono (del-delayᶜ d)           = del-delayᶜ' (≼-cost-mono d)
≼-cost-mono (use-delayᶜ p d)         = use-delayᶜ' p (≼-cost-mono d)

-- the sub-trace order proper (no slack)

≼-cost-mono₀ : {s t : Trace} → s ≼ᶜ t → s ≼ᶜ' t
≼-cost-mono₀ = ≼-cost-mono

------------------------------------------------------------------------
-- Bounding the duration at the larger cost
--
-- A demand met when operations are charged `c` is still met when they
-- are charged the dearer `c'`, so the larger cost bounds durations too.

duration-slack-hi : ∀ {k s t} → s ≼[ k ]ᶜ t → duration s ≤ duration t + k
duration-slack-hi d = duration-slack (≼-cost-mono d)
