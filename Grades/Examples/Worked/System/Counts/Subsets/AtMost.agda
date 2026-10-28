------------------------------------------------------------------------
-- Worked instance of the subset cap, projected onto quotas.          --
--                                                                    --
-- Each counter takes the greatest count among the listed runs.       --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Counts.Subsets.AtMost where

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; ⌈_⌉; ⟅_⟆; ⟅_∣_⟆; poll; uplink;
         chatty-uplink; write; send; pause)
open import Grades.Examples.Worked.Counts.Index using (index; ⟪_,_,_⟫ᵐ)
open import Grades.Examples.Worked.Traces.Subsets.RightSided
  using (permitting_; any-run)
open import Grades.Examples.Counts.AtMost using (upto; unlimited)
open import Grades.Examples.System.Counts.Subsets.AtMost
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans index
  using (subsets→at-most-counts)

open _→ᵍ_ subsets→at-most-counts using (map)

-- a reading, and possibly a transmission

poll-or-uplink : map (permitting ⟅ poll ∣ uplink ⟆) ≡ ⟪ upto 1 , upto 0 , upto 1 ⟫ᵐ
poll-or-uplink = refl

-- transmitting twice

chatty : map (permitting ⟅ chatty-uplink ⟆) ≡ ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ
chatty = refl

-- a write or a transmission: each counter is maximised on its own,
-- so the quota allows both, which neither run performs

write-or-send : map (permitting ⟅ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆) ≡ ⟪ upto 0 , upto 1 , upto 1 ⟫ᵐ
write-or-send = refl

-- a pause draws on nothing, and any run at all needs no quota

pausing : map (permitting ⟅ pause ⟆) ≡ ⟪ upto 0 , upto 0 , upto 0 ⟫ᵐ
pausing = refl

unrestricted : map any-run ≡ ⟪ unlimited , unlimited , unlimited ⟫ᵐ
unrestricted = refl
