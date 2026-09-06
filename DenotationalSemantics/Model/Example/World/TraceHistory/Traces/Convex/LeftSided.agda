------------------------------------------------------------------------
-- A trace-history Kripke frame for convexly ordered sets of traces as  --
-- the resource grades.                                                 --
--                                                                    --
-- Worlds and accessibility are those of `LowerLift.LeftSided`:          --
-- `w ⊑ʰ[ P ] w'` asks for a continuation that covers *every* member    --
-- of `P`. That relation is covariant along the floor order, and the    --
-- convex order has the floor order as its first conjunct, so `⊑-mono`  --
-- is that half of it. The second, Smyth, conjunct is not read by the   --
-- frame: it constrains which coercions are derivable, not which worlds --
-- a grade reaches.                                                     --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Convex.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.Product using (proj₁)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Example.Traces.Convex.LeftSided Op _≟ₒ_ c using (convex-left-sided)

open import DenotationalSemantics.Model.World

open import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.LowerLift.LeftSided
  Op _≟ₒ_ c using (_⊑ʰ[_]_; ⊑ʰ-refl; ⊑ʰ-trans; ⊑ʰ-mono; ⊑ʰ-irrelevant)

histories : World convex-left-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ʰ[_]_
  ; ⊑-refl        = ⊑ʰ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} rel → ⊑ʰ-mono {ρ₁} {ρ₂} (proj₁ rel)
  ; ⊑-irrelevant  = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
