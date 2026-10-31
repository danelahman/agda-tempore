------------------------------------------------------------------------
-- A coverage order on timed traces, relative to a `costˡᵒ` on        --
-- operation symbols.                                                 --
--                                                                    --
-- `s ≼ᶜ t` reads: the run `t` covers the trace `s`. Every operation  --
-- `s` names must occur in `t`, in order, never bought with time, and --
-- every delay `s` names must be covered by what `t` does             --
-- between the same two operations it names, unmatched operations     --
-- counting at their execution time. So `⟨ n ⟩ ≼ᶜ t` as soon as `t`   --
-- spends `n` where `s` asks for it, and `⌈ o ⌉ ≼ᶜ t` only when `t`   --
-- performs `o`.                                                      --
--                                                                    --
-- This is the order a guarantee wants. It is not the converse of     --
-- `Traces.Allowance`, where a bound's delays buy the run's           --
-- operations: read as a guarantee, that would let a run that only    --
-- idles discharge "a reading was taken".                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Coverage
  {D : Duration} (T : TimeDomain D) (Op : Set) (costˡᵒ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

-- The relation itself, and its preorder structure: reflexivity at any
-- slack, weakening to more slack, and transitivity adding the slacks.

open import Grades.Traces.Coverage.Core T Op costˡᵒ public

-- The moves, with monotonicity of the trace product in its pinned form.

open import Grades.Traces.Coverage.Moves T Op costˡᵒ public

-- How the order bounds durations, and what a spent run covers.

open import Grades.Traces.Coverage.Duration T Op costˡᵒ public

-- The decision procedure, given decidable equality of operation names.

open import Grades.Traces.Coverage.Decidable T Op costˡᵒ public
