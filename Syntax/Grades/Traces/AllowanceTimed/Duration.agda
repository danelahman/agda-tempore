------------------------------------------------------------------------
-- Durations along the time-strict allowance order.                    --
--                                                                    --
-- Both facts are inherited through the embedding into the lenient     --
-- order: a run permitted time-strictly is permitted leniently, so it  --
-- is no longer than its bound, and the empty bound permits nothing    --
-- but the empty run.                                                  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)

open import Util.Equality

module Syntax.Grades.Traces.AllowanceTimed.Duration (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op

open import Syntax.Grades.Traces.Allowance.Duration Op cost
  using (duration-≼ᵃ; ≼ᵃ-ε-inv)
open import Syntax.Grades.Traces.AllowanceTimed.Core Op cost

open Durations cost

duration-≼ᵃᵗ : {s t : Trace} → s ≼ᵃᵗ t → duration s ≤ duration t
duration-≼ᵃᵗ d = duration-≼ᵃ (≼ᵃᵗ→≼ᵃ d)

≼ᵃᵗ-ε-inv : ((o : Op) → 0 < cost o) → {s : Trace} → s ≼ᵃᵗ ε → s ≡ ε
≼ᵃᵗ-ε-inv pos d = ≼ᵃ-ε-inv pos (≼ᵃᵗ→≼ᵃ d)
