------------------------------------------------------------------------
-- Worked instance of the finite run set cap, projected onto at-least --
-- counts.                                                            --
--                                                                    --
-- Each counter takes the least count among the listed runs, and      --
-- `any-run` makes no claim.                                          --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Counts.FiniteRunSets.AtLeast where

open import Data.Vec.Base using ([]; _∷_)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open import Grades.Examples.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; ⟅_∣_⟆; poll; uplink)
open import Grades.Examples.Worked.Counts.Index using (index)
open import Grades.Examples.Worked.Traces.FiniteRunSets.UpperBound
  using (permitting_; any-run)
import Grades.Examples.Counts.AtLeast as AtLeast
open AtLeast using (certainly; no-claim)
open import Grades.Examples.System.Counts.FiniteRunSets.AtLeast
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans index
  using (finite-run-sets→at-least-counts-with-⊤)

open _→ᵍ_ finite-run-sets→at-least-counts-with-⊤ using (map)

-- polling or uplinking: the reading is certain, the transmission not

poll-or-uplink :
  map (permitting ⟅ poll ∣ uplink ⟆) ≡ certainly 1 ∷ certainly 0 ∷ certainly 0 ∷ []
poll-or-uplink = refl

unrestricted : map any-run ≡ no-claim ∷ no-claim ∷ no-claim ∷ []
unrestricted = refl
