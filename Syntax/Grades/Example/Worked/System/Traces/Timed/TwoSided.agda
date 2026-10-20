------------------------------------------------------------------------
-- Worked instance: keeping both endpoints.                           --
--                                                                    --
-- `System.Traces.Timed.TwoSided` is the pairing of the two timed     --
-- projections. Its image is a time interval by the coherence field   --
-- of the grade, run consistency, which puts the fastest guarantee no --
-- slower than the slowest allowance.                                 --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Traces.Timed.TwoSided where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)

open import Relation.Nullary.Decidable using (True)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; _≾ᵢ_; _·ᵢ_; ↑_)
  renaming ([_,_] to mkᵢ)

-- every window below has a finite upper endpoint

[_,_] : (m n : ℕ) {m≤n : True (m ≤? n)} → Interval∞
[ m , n ] {m≤n} = mkᵢ m (↑ n) {m≤n}

open import Syntax.Grades.Example.System.Traces.Timed.TwoSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos
  using (two-sided-traces→intervals)

open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
  using () renaming (⟅_⟆ to ⟅_⟆ˡᵒ; ⟅_∣_⟆ to ⟅_∣_⟆ˡᵒ)
open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
  using (within_)
  renaming (⟅_⟆ to ⟅_⟆ʰⁱ; ⟅_∣_⟆ to ⟅_∣_⟆ʰⁱ)

open import Syntax.Grades.Example.Worked.Traces.Timed.TwoSided
  using (exact; _·ᵗˢ_) renaming ([_,_] to ⟪_,_⟫; holds to holdsᵗˢ)

-- a contract that guarantees a reading and permits it six ticks' more
-- work becomes the window between one tick and seven

contract-measured :
  map two-sided-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ⟫
  ≡ [ 1 , 7 ]
contract-measured = refl

-- listing alternatives enlarges the window at both ends at once, each end
-- aggregating its own way

alternatives-measured-both :
  map two-sided-traces→intervals
      ⟪ ⟅ ⌈ read ⌉ ∣ ⌈ send ⌉ ⟆ˡᵒ
      , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∣ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ʰⁱ ⟫
  ≡ [ 1 , 12 ]
alternatives-measured-both = refl

-- a grade whose two endpoints coincide still becomes a window, the two
-- cost models pulling its ends apart: a reading and a store are certain
-- to take three ticks and may take four

exact-measured :
  map two-sided-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
               ≡ [ 3 , 4 ]
exact-measured = refl

-- monotonicity: a computation known to take a reading and a store sits
-- inside the contract's window

window-contains :
  map two-sided-traces→intervals (exact (⌈ read ⌉ ∙ ⌈ write ⌉))
  ≾ᵢ map two-sided-traces→intervals
         ⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ⟫
window-contains =
  map-monotone two-sided-traces→intervals
               {exact (⌈ read ⌉ ∙ ⌈ write ⌉)}
               {⟪ ⟅ ⌈ read ⌉ ⟆ˡᵒ , within ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ⟆ʰⁱ ⟫}
               (holdsᵗˢ _ _)

-- and it is a monoid map: sequencing before or after measuring agrees

windows-add :
  map two-sided-traces→intervals (exact ⌈ read ⌉ ·ᵗˢ exact ⌈ send ⌉)
  ≡ map two-sided-traces→intervals (exact ⌈ read ⌉)
    ·ᵢ map two-sided-traces→intervals (exact ⌈ send ⌉)
windows-add = refl
