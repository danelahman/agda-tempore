------------------------------------------------------------------------
-- A free operation, and why the allowance order asks for a positive  --
-- cost model.                                                        --
--                                                                    --
-- `Traces.Allowance` is parameterised by `costʰⁱ` alone, but         --
-- `Allowance.Antisym` and `Allowance.AsOrder` ask in addition that   --
-- every operation cost something.                                    --
--                                                                    --
-- At an operation `o` with `costʰⁱ o ≡ 0`, the bound `ε` permits the --
-- run `⌈ o ⌉`: `use-op` pays for the operation out of an empty       --
-- budget. Both facts about the unit the grade construction reads     --
-- then fail. The empty bound permits a run different from itself, so --
-- `≼-ε-inv` is false, and since `ε` is permitted by every bound, two --
-- distinct traces permit each other, so `≼-antisym` is false too.    --
-- `FreeOperation` exhibits each as a checked term.                   --
--                                                                    --
-- The failure is one of the cost model, not of the allowance order:  --
-- at a positive cost model `Allowance.Antisym` and                   --
-- `Allowance.Duration` supply both fields.                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Allowance.ZeroCost
  {D : Duration} (T : TimeDomain D) (Op : Set) (costʰⁱ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Grades.Traces.Base T Op
open import Grades.Traces.Allowance T Op costʰⁱ

------------------------------------------------------------------------
-- What a free operation permits
--
-- One operation costing nothing suffices.

module FreeOperation (o : Op) (free : costʰⁱ o ≡ 0ᴰ) where

  -- its running time fits inside an empty budget

  free≤0 : costʰⁱ o ≤ 0ᴰ
  free≤0 = ≤-reflexive free

  -- so the spent bound `ε` permits the run that performs `o`

  op≼ε : ⌈ o ⌉ ≼ᵃ ε
  op≼ε = use-op free≤0 nil

  -- while `ε` is permitted by every bound, this one included

  ε≼op : ε ≼ᵃ ⌈ o ⌉
  ε≼op = nil

  -- and the two traces are distinct

  op≢ε : ¬ (⌈ o ⌉ ≡ ε)
  op≢ε ()

  -- the empty bound therefore permits more than the empty run, which
  -- is the `≼-ε-inv` field of `TraceOrder` and what the grades'
  -- zero-product law rests on

  ¬-≼ᵃ-ε-inv : ¬ ({s : Trace} → s ≼ᵃ ε → s ≡ ε)
  ¬-≼ᵃ-ε-inv ε-inv = op≢ε (ε-inv op≼ε)

  -- and two distinct traces permit each other, which is the
  -- `≼-antisym` field of `TracePartialOrder`

  ¬-≼ᵃ-antisym : ¬ ({s t : Trace} → s ≼ᵃ t → t ≼ᵃ s → s ≡ t)
  ¬-≼ᵃ-antisym antisym = op≢ε (antisym op≼ε ε≼op)
