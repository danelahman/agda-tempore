------------------------------------------------------------------------
-- Worked instance of the subset cap, projected onto certain counts.    --
--
-- Each counter takes the least count among the listed runs, and any    --
-- run at all makes no claim.                                           --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Counts.Subsets.AtLeast where

open import Data.Vec.Base using ([]; _∷_)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; ⟅_∣_⟆; poll; uplink)
open import Syntax.Grades.Example.Worked.Counts.Index using (index)
open import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided
  using (permitting_; any-run)
import Syntax.Grades.Example.Counts.AtLeast as AtLeast
open AtLeast using (certainly; no-claim)
open import Syntax.Grades.Example.System.Counts.Subsets.AtLeast
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans index
  using (subsets→at-least-counts-with-⊤)

open _→ᵍ_ subsets→at-least-counts-with-⊤ using (map)

-- polling or uplinking: the reading is certain, the transmission not

poll-or-uplink :
  map (permitting ⟅ poll ∣ uplink ⟆) ≡ certainly 1 ∷ certainly 0 ∷ certainly 0 ∷ []
poll-or-uplink = refl

unrestricted : map any-run ≡ no-claim ∷ no-claim ∷ no-claim ∷ []
unrestricted = refl
