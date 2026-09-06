------------------------------------------------------------------------
-- A trace-history Kripke frame for convexly ordered caps.             --
--                                                                    --
-- Worlds and accessibility are those of `LowerLift.RightSided`:        --
-- `w ⊑ʰ[ P ] w'` asks for a continuation that fits inside *some*       --
-- member of `P`. That relation is covariant along the Hoare cap order, --
-- and `Convex.RightSided` has that order as its first conjunct, so     --
-- `⊑-mono` is that half of it.                                        --
--                                                                    --
-- The second, Smyth, conjunct would serve just as well, read through   --
-- `UpperLift.RightSided`'s universal frame instead -- which is the     --
-- same choice `Convex.LeftSided` offers between its two frames.        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Convex.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.Product using (proj₁)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Example.Traces.Convex.RightSided Op _≟ₒ_ c
  using (convex-right-sided)

open import DenotationalSemantics.Model.World

open import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.LowerLift.RightSided
  Op _≟ₒ_ c using (_⊑ʳ[_]_; ⊑ʳ-refl; ⊑ʳ-trans; ⊑ʳ-mono; ⊑ʳ-irrelevant)

histories : World convex-right-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ʳ[_]_
  ; ⊑-refl        = ⊑ʳ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ʳ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} rel → ⊑ʳ-mono {ρ₁} {ρ₂} (proj₁ rel)
  ; ⊑-irrelevant  = λ {ρ} → ⊑ʳ-irrelevant {ρ}
  }
