------------------------------------------------------------------------
-- Worked instance of the allowance cap: delays cover operations.     --
--                                                                    --
-- The bound `⟨ 2 ⟩` permits a reading, which takes one tick. Every   --
-- grade morphism into quotas sends `⟨ 2 ⟩` to the unit, and          --
-- therefore sends `⌈ read ⌉` to the unit.                            --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Counts.Timed.RightSided where

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costʰⁱ; costʰⁱ-pos; ⌈_⌉; ⟨_⟩; read)
open import Syntax.Grades.Example.Worked.Counts.Index using (index)
open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
  using (within_; ⟅_⟆; _≾_; holds)
open import Syntax.Grades.Example.System.Counts.Timed.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos index
  using (erases; miscounts)

import Syntax.Grades.Example.Counts.AtMost as AtMost
open AtMost using (at-most-counts)

a-delay-permits-a-reading : within ⟅ ⌈ read ⌉ ⟆ ≾ within ⟅ ⟨ 2 ⟩ ⟆
a-delay-permits-a-reading = holds

reading-erased : (F : _ →ᵍ at-most-counts 3) → _→ᵍ_.map F (within ⟅ ⌈ read ⌉ ⟆) ≡ AtMost.uᵛ
reading-erased F = erases F read
