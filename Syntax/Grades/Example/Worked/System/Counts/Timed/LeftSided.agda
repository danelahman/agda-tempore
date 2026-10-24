------------------------------------------------------------------------
-- Worked instance of the coverage floor, projected onto certain      --
-- counts.                                                            --
--                                                                    --
-- Each counter takes the least count among the listed guarantees.    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Counts.Timed.LeftSided where

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costˡᵒ; logged; uplink; chatty-uplink; pause)
open import Syntax.Grades.Example.Worked.Counts.Index using (index; ⟪_,_,_⟫ˡ)
open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided
  using (⟅_⟆; ⟅_∣_⟆)
open import Syntax.Grades.Example.System.Counts.Timed.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ index
  using (left-sided→at-least-counts)

open _→ᵍ_ left-sided→at-least-counts using (map)

-- stored or transmitted: the reading is certain, neither of the rest

logged-or-uplink : map ⟅ logged ∣ uplink ⟆ ≡ ⟪ 1 , 0 , 0 ⟫ˡ
logged-or-uplink = refl

-- two transmissions certain

chatty : map ⟅ chatty-uplink ⟆ ≡ ⟪ 1 , 0 , 2 ⟫ˡ
chatty = refl

-- a guarantee of time alone makes no count certain

pausing : map ⟅ pause ⟆ ≡ ⟪ 0 , 0 , 0 ⟫ˡ
pausing = refl
