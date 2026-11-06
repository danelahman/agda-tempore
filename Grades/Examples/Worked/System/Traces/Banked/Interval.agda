------------------------------------------------------------------------
-- Worked instance: keeping both endpoints.                           --
--                                                                    --
-- `System.Traces.Banked.Interval` is the pairing of the two timed    --
-- projections. Its image is a time interval by the coherence field   --
-- of the grade, run consistency, which puts the fastest guarantee no --
-- slower than the slowest allowance.                                 --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.Banked.Interval where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)

open import Relation.Nullary.Decidable using (True)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Grades.Examples.Time.Interval
  using (Interval∞; _≾ᵢ_; _·ᵢ_; ↑_)
  renaming ([_,_] to mkᵢ)

-- every window below has a finite upper endpoint

[_,_] : (m n : ℕ) {m≤n : True (m ≤? n)} → Interval∞
[ m , n ] {m≤n} = mkᵢ m (↑ n) {m≤n}

open import Grades.Examples.System.Traces.Banked.Interval
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos
  using (interval-traces→intervals)

open import Grades.Examples.Worked.Traces.Banked.LowerBound
  using () renaming (⟅_⟆ to ⟅_⟆ˡᵒ; ⟅_∣_⟆ to ⟅_∣_⟆ˡᵒ)
open import Grades.Examples.Worked.Traces.Banked.UpperBound
  using (within_)
  renaming (⟅_⟆ to ⟅_⟆ʰⁱ; ⟅_∣_⟆ to ⟅_∣_⟆ʰⁱ)

open import Grades.Examples.Worked.Traces.Banked.Interval
  using (exact; _·ᵗˢ_) renaming ([_,_] to ⟪_,_⟫; holds to holdsᵗˢ)

-- a contract that guarantees a reading and permits it six ticks' more
-- work becomes the window between one tick and seven

contract-measured :
  map interval-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ⟫
  ≡ [ 1 , 7 ]
contract-measured = refl

-- listing alternatives enlarges the window at both ends at once, each end
-- aggregating its own way

alternatives-measured-both :
  map interval-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ˡᵒ
      , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ʰⁱ ⟫
  ≡ [ 1 , 12 ]
alternatives-measured-both = refl

-- a grade whose two endpoints coincide still becomes a window, the two
-- cost models pulling its ends apart: a reading and a store are certain
-- to take three ticks and may take four

exact-measured :
  map interval-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
               ≡ [ 3 , 4 ]
exact-measured = refl

-- monotonicity: a computation known to take a reading and a store sits
-- inside the contract's window

window-contains :
  map interval-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
  ≾ᵢ map interval-traces→intervals
         ⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ⟫
window-contains =
  map-monotone interval-traces→intervals
               {exact (⌈ read ⌉ ∙ ⌈ write ⌉)}
               {⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ⟫}
               (holdsᵗˢ _ _)

-- and it is a monoid map: sequencing before or after measuring agrees

windows-add :
  map interval-traces→intervals (exact ⌈ read ⌉ ·ᵗˢ exact ⌈ send ⌉)
  ≡ map interval-traces→intervals (exact ⌈ read ⌉)
    ·ᵢ map interval-traces→intervals (exact ⌈ send ⌉)
windows-add = refl
