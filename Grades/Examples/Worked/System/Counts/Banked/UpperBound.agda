------------------------------------------------------------------------
-- Worked instance of the allowance cap: delays cover operations.     --
--                                                                    --
-- The bound `⟨ 2 ⟩` permits a reading, which takes one tick. Every   --
-- grade morphism into quotas sends `⟨ 2 ⟩` to the unit, and          --
-- therefore sends `⌈ read ⌉` to the unit.                            --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Counts.Banked.UpperBound where

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costʰⁱ; costʰⁱ-pos; ⌈_⌉; ⟨_⟩; read)
open import Grades.Examples.Worked.Counts.Index using (index)
open import Grades.Examples.Worked.Traces.Banked.UpperBound
  using (within_; ⟅_⟆; _≾_; holds)
open import Grades.Examples.System.Counts.Banked.UpperBound
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos index
  using (erases; miscounts)

import Grades.Examples.Counts.AtMost as AtMost
open AtMost using (at-most-counts)

a-delay-permits-a-reading : within ⟅ ⌈ read ⌉ ⟆ ≾ within ⟅ ⟨ 2 ⟩ ⟆
a-delay-permits-a-reading = holds

reading-erased : (F : _ →ᵍ at-most-counts 3) → AtMost._≃ᵛ_ (_→ᵍ_.map F (within ⟅ ⌈ read ⌉ ⟆)) AtMost.𝟏ᵛ
reading-erased F = erases F read
